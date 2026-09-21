/*
 * Maze Builder - sim.js
 * A deterministic simulation of one floor of Maze of Gains v2 (playmog.xyz), pure logic, no DOM.
 * Defines window.MOG_SIM in the browser and module.exports under Node. ES5 only (no build step).
 *
 * Sources of truth, in this order: extension/src/data.js (V2_ENEMY_CONFIGS numbers), docs/CLIENT_ANALYSIS.md,
 * docs/CLIENT_ANALYSIS_2.md, extension/src/engine.js (phase model, lockHit, ghosts, frogspawn shield),
 * site/copy.json (official English names), docs/RUN_OBSERVATIONS.md. Where the docs are silent the value used
 * is written into RULES.<table>.<key>.note so the UI can show it.
 *
 * PUBLIC API (see site/builder/CONTRACT.md)
 *   MOG_SIM.RULES                  tables: ENEMIES, OBJECTS, PICKUPS, TRAPS, ITEMS, WEATHER, TALENTS, HERO, LIMITS
 *   MOG_SIM.validate(spec)         -> { ok, errors: [] }
 *   MOG_SIM.newGame(spec)          -> state (RNG seeded from the encoded spec; a shared floor replays identically)
 *   MOG_SIM.actions(state)         -> [ { id, kind, label, target, enabled, why, sub, cost, dir, item, dirs } ]
 *   MOG_SIM.step(state, id, opts)  -> { state, events }   never mutates the input state
 *       id: 'up' | 'down' | 'left' | 'right' | 'pass' | 'item:<key>'
 *       opts (optional, third argument): { dir: 'up'|'down'|'left'|'right' } for directional items, e.g.
 *       step(state, 'item:single_shot', { dir: 'left' }). Without a dir the item press is refused (event 'blocked').
 *   MOG_SIM.cues(state)            -> [ { x, y, kind: 'target'|'aoe'|'explode'|'line', enemyId } ]  what the game
 *                                     telegraphs right now. Under heatwave (mirage) the zones are still returned, only
 *                                     the timing is unreliable: the UI should print enemy.turns as "?".
 *   MOG_SIM.encode(spec) / decode(str)   URL safe string (base64url of compact JSON) and back (null if broken)
 *   MOG_SIM.sample(name?)          -> a ready made 14x9 floor: 'gauntlet' (default), 'frog pond', 'dragma hall'
 *   MOG_SIM.SAMPLES                -> the sample names
 *
 * TURN ORDER inside step(): hero press -> hero effects (damage, smash drops, pickups, stairs) -> traps and bombs
 * tick -> every enemy acts in id order (phase machine) -> pickups despawn tick -> status check.
 * state.turn increases after every accepted press. Blocked presses (wall, ghost tile, missing dir) cost nothing.
 *
 * ENEMY PHASES: idle -> charge(turns) -> attack (this turn it already fired) -> rest(turns) -> idle -> ...
 * A wind-up fixes target/dir/zone when it starts. The hit lands on the enemy tick in which turns reaches 0, so an
 * enemy shown with charge(1) hits at the END of the hero's next press (one press to leave). A kill cancels the
 * wind-up. Ghosts (maxHp 0) are invincible: nothing can be done into their tile.
 */
(function (root) {
  'use strict';

  /* ===================================================================================================
   * 1. Small helpers: directions, cloning, hashing, seeded RNG, base64url
   * =================================================================================================== */
  var DIRS = {
    up: { dx: 0, dy: -1, arrow: '↑', word: 'up' },
    down: { dx: 0, dy: 1, arrow: '↓', word: 'down' },
    left: { dx: -1, dy: 0, arrow: '←', word: 'left' },
    right: { dx: 1, dy: 0, arrow: '→', word: 'right' }
  };
  var DIR_IDS = ['up', 'down', 'left', 'right'];
  var OPPOSITE = { up: 'down', down: 'up', left: 'right', right: 'left' };

  function clone(o) { return JSON.parse(JSON.stringify(o)); }
  function isInt(n) { return typeof n === 'number' && isFinite(n) && Math.floor(n) === n; }
  function cheb(ax, ay, bx, by) { return Math.max(Math.abs(ax - bx), Math.abs(ay - by)); }
  function manh(ax, ay, bx, by) { return Math.abs(ax - bx) + Math.abs(ay - by); }
  function has(arr, v) { return arr.indexOf(v) >= 0; }

  var imul = Math.imul || function (a, b) {
    var ah = (a >>> 16) & 0xffff, al = a & 0xffff, bh = (b >>> 16) & 0xffff, bl = b & 0xffff;
    return (al * bl) + (((ah * bl + al * bh) << 16) >>> 0) | 0;
  };
  function hash32(str) { // FNV-1a
    var h = 0x811c9dc5, i;
    for (i = 0; i < str.length; i++) { h ^= str.charCodeAt(i); h = imul(h, 0x01000193); }
    return h >>> 0;
  }
  function rngNext(st) { // mulberry32 over state.rng, so every roll is part of the replayable state
    var t = (st.rng = (st.rng + 0x6D2B79F5) | 0);
    t = imul(t ^ (t >>> 15), t | 1);
    t ^= t + imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }
  function rngInt(st, lo, hi) { return lo + Math.floor(rngNext(st) * (hi - lo + 1)); }
  function rngPick(st, arr) { return arr.length ? arr[Math.floor(rngNext(st) * arr.length)] : null; }

  var B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_';
  function utf8Bytes(str) {
    var out = [], i, c;
    for (i = 0; i < str.length; i++) {
      c = str.charCodeAt(i);
      if (c >= 0xd800 && c <= 0xdbff && i + 1 < str.length) { c = 0x10000 + ((c - 0xd800) << 10) + (str.charCodeAt(i + 1) - 0xdc00); i++; }
      if (c < 0x80) out.push(c);
      else if (c < 0x800) out.push(0xc0 | (c >> 6), 0x80 | (c & 63));
      else if (c < 0x10000) out.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63));
      else out.push(0xf0 | (c >> 18), 0x80 | ((c >> 12) & 63), 0x80 | ((c >> 6) & 63), 0x80 | (c & 63));
    }
    return out;
  }
  function utf8Str(bytes) {
    var out = '', i = 0, c, n;
    while (i < bytes.length) {
      c = bytes[i++];
      if (c < 0x80) n = c;
      else if (c < 0xe0) n = ((c & 31) << 6) | (bytes[i++] & 63);
      else if (c < 0xf0) n = ((c & 15) << 12) | ((bytes[i++] & 63) << 6) | (bytes[i++] & 63);
      else { n = ((c & 7) << 18) | ((bytes[i++] & 63) << 12) | ((bytes[i++] & 63) << 6) | (bytes[i++] & 63); n -= 0x10000; out += String.fromCharCode(0xd800 + (n >> 10), 0xdc00 + (n & 1023)); continue; }
      out += String.fromCharCode(n);
    }
    return out;
  }
  function b64Encode(bytes) {
    var out = '', i, a, b, c;
    for (i = 0; i < bytes.length; i += 3) {
      a = bytes[i]; b = i + 1 < bytes.length ? bytes[i + 1] : 0; c = i + 2 < bytes.length ? bytes[i + 2] : 0;
      out += B64.charAt(a >> 2) + B64.charAt(((a & 3) << 4) | (b >> 4));
      out += i + 1 < bytes.length ? B64.charAt(((b & 15) << 2) | (c >> 6)) : '';
      out += i + 2 < bytes.length ? B64.charAt(c & 63) : '';
    }
    return out;
  }
  function b64Decode(str) {
    var out = [], i, v = [], j, k;
    str = String(str).replace(/=+$/, '').replace(/\+/g, '-').replace(/\//g, '_');
    for (i = 0; i < str.length; i += 4) {
      for (j = 0; j < 4; j++) { k = B64.indexOf(str.charAt(i + j)); if (i + j < str.length && k < 0) return null; v[j] = k < 0 ? 0 : k; }
      out.push((v[0] << 2) | (v[1] >> 4));
      if (i + 2 < str.length) out.push(((v[1] & 15) << 4) | (v[2] >> 2));
      if (i + 3 < str.length) out.push(((v[2] & 3) << 6) | v[3]);
    }
    return out;
  }

  /* ===================================================================================================
   * 2. RULES: names, numbers and one line descriptions the UI shows (official names from site/copy.json)
   * =================================================================================================== */
  var AGGRO_NOTE = 'aggro is the larger of the x and y distance to you (Chebyshev).';
  function enemy(name, short, o) {
    o.name = name; o.short = short;
    if (o.implemented === undefined) o.implemented = true;
    if (o.aggro === undefined) o.aggro = 0;
    if (o.wander === undefined) o.wander = false;
    if (o.rooted === undefined) o.rooted = false;
    if (o.invincible === undefined) o.invincible = false;
    return o;
  }
  var ENEMIES = {
    smallslime: enemy('Small slime', '15 HP. Winds up a 3-5 dmg strike at an adjacent tile over 2 turns', { hp: 15, dmg: [3, 5], range: 1, charge: 2, rest: 1, kind: 'melee', wander: true, note: 'No aggro in the data: it wanders and only winds up when you end a turn next to it.' }),
    mediumslime: enemy('Orange slime', '25 HP. Winds up a 5-8 dmg strike at an adjacent tile over 1 turn', { hp: 25, dmg: [5, 8], range: 1, charge: 1, rest: 1, kind: 'melee', wander: true, note: 'No aggro in the data: it wanders and only winds up when you end a turn next to it.' }),
    bat: enemy('Bat', '30 HP. Telegraphs a dash of up to 4 tiles along its row or column, 7-10 dmg', { hp: 30, dmg: [7, 10], range: 4, charge: 1, rest: 1, kind: 'dash', wander: true, note: 'Dash lines stop at walls only. After the dash it lands on the last free tile of the line, or just before you.' }),
    skelechump: enemy('Club skeleton', '45 HP. Winds up a 10-12 dmg strike at the adjacent tile it targeted over 2 turns', { hp: 45, dmg: [10, 12], range: 1, charge: 2, rest: 1, kind: 'melee', aggro: 4, note: 'Steps toward you while you are within 4. ' + AGGRO_NOTE }),
    skelesoldier: enemy('Armored skeleton', '60 HP. Strikes its target tile and all four tiles directly beside it at once, 12-15 dmg', { hp: 60, dmg: [12, 15], range: 1, charge: 1, rest: 1, kind: 'aoe', aggro: 4, note: 'The cross is the 4 tiles around the skeleton. Its hit lands at the end of the press after charge(1): one press to step away, a diagonal step is safe.' }),
    dragma_bat: enemy('Dragma Bat', '35 HP. Telegraphs a dash of up to 10 tiles along its row or column, 10-12 dmg', { hp: 35, dmg: [10, 12], range: 10, charge: 1, rest: 1, kind: 'dash', wander: true, note: 'Dash lines stop at walls only.' }),
    dragma_skelechump: enemy('Dragma Chump', '50 HP. Winds up a 12-15 dmg strike at the adjacent tile it targeted over 2 turns', { hp: 50, dmg: [12, 15], range: 1, charge: 2, rest: 1, kind: 'melee', aggro: 10, note: 'Steps toward you while you are within 10. ' + AGGRO_NOTE }),
    dragma_skelesoldier: enemy('Dragma Soldier', '70 HP. Strikes its target tile and all four tiles directly beside it at once, 15-17 dmg', { hp: 70, dmg: [15, 17], range: 1, charge: 1, rest: 1, kind: 'aoe', aggro: 10, note: 'Same cross as the Armored skeleton, aggro 10.' }),
    ghost1: enemy('Party-hat ghost', 'Invulnerable. Follows slowly and blocks its tile without attacking, 0 dmg, moves every 2 turns', { hp: 0, dmg: [0, 0], range: 0, charge: 0, rest: 0, kind: 'passive', aggro: 4, every: 2, invincible: true, note: 'Floats over pots and drops. Nothing can be done into its tile.' }),
    ghost2: enemy('Pale ghost', 'Invulnerable. Follows slowly and winds up adjacent strikes for 5 dmg, moves every 2 turns, blocks its tile', { hp: 0, dmg: [5, 5], range: 1, charge: 1, rest: 1, kind: 'melee', aggro: 3, every: 2, invincible: true, note: 'Floats over pots and drops. Nothing can be done into its tile.' }),
    ghost3: enemy('Hooded ghost', 'Invulnerable. Follows more slowly and lands heavier adjacent strikes for 8 dmg, moves every 3 turns, blocks its tile', { hp: 0, dmg: [8, 8], range: 1, charge: 1, rest: 1, kind: 'melee', aggro: 3, every: 3, invincible: true, note: 'Floats over pots and drops. Nothing can be done into its tile.' }),
    mimic: enemy('Chest mimic', '30 HP. Hides as a chest and ambushes an adjacent player when revealed, 7-10 dmg', { hp: 30, dmg: [7, 10], range: 1, charge: 2, rest: 1, kind: 'melee', aggro: 4, ambush: true, note: 'Stays still until you stand next to it once, then chases like a Club skeleton.' }),
    potmimick: enemy('Pot mimic', '30 HP. Hides as a pot and ambushes an adjacent player when revealed, 3-5 dmg', { hp: 30, dmg: [3, 5], range: 1, charge: 1, rest: 1, kind: 'melee', aggro: 4, ambush: true, note: 'Also 5 percent of smashed pots turn out to be one.' }),
    skelearcher: enemy('Skeleton archer', '20 HP. Fires arrows along its row or column for 12-15, then retreats', { hp: 20, dmg: [12, 15], range: 6, charge: 2, rest: 1, kind: 'projectile', aggro: 3, flee: 5, note: 'Winds up when you stand on its row or column within 6 tiles (assumed: the data lists range 1). Here the arrow lands the turn the wind-up ends; in the game it is a projectile that flies on. After firing it runs away for 5 turns.' }),
    boomcap: enemy('Exploding mushroom', '10 HP. Follows you for 4 turns, then stops and explodes 3x3 for 7-10', { hp: 10, dmg: [7, 10], range: 1, charge: 4, rest: 0, kind: 'explode', aggro: 6, note: 'Steps toward you on every timer turn except the last, then blows up and dies. Kill it in one hit before the timer ends.' }),
    lobcap: enemy('Lobbing mushroom', '30 HP. Stays in place and throws exploding mushrooms onto tiles near you', { hp: 30, dmg: [0, 0], range: 1, charge: 4, rest: 0, kind: 'thrower', aggro: 6, rooted: true, note: 'Every 4 turns while you are within 6 it throws an Exploding mushroom onto a free tile next to you. The cap of 2 alive at once is assumed.' }),
    whipweed: enemy('Whip plant', '30 HP. Stays in place and lashes along one marked direction, reaching up to 2 tiles, 12-15 dmg', { hp: 30, dmg: [12, 15], range: 2, charge: 2, rest: 1, kind: 'reach', aggro: 2, rooted: true, note: 'Rooted. Winds up when you stand in a straight line within 2 tiles.' }),
    megawhipweed: enemy('Large whip plant', '60 HP. Holds its ground and lashes along one marked direction, reaching up to 3 tiles, 18-20 dmg', { hp: 60, dmg: [18, 20], range: 3, charge: 2, rest: 1, kind: 'reach', aggro: 3, rooted: true, note: 'Rooted. Winds up when you stand in a straight line within 3 tiles.' }),
    frogglet: enemy('Blue frog', '40 HP. Hops between nearby tiles, landing on you deals 8-12', { hp: 40, dmg: [8, 12], range: 1, charge: 2, rest: 0, kind: 'hop', note: 'Stands still until you are next to it, then hops onto your tile after 2 turns. No rest. Live Blue frogs shield every Frog egg cluster.' }),
    frogspawn: enemy('Frog egg cluster', '80 HP. Produces blue frogs, and a shield protects it while any of its frogs is alive', { hp: 80, dmg: [0, 0], range: 1, charge: 5, rest: 0, kind: 'spawner', aggro: 8, rooted: true, note: 'Spawns a Blue frog on a free neighbour tile every 5 turns while you are within 8, 4 spawns in total. Shield = number of live Blue frogs on the floor.' }),
    croaker: enemy('Hat-wearing frog', '50 HP. Prepares short hops toward you, landing on you deals 12-15', { hp: 50, dmg: [12, 15], range: 1, charge: 2, rest: 0, kind: 'leap', aggro: 4, wander: true, note: 'Steps toward you within 4, leaps onto your tile after 2 turns of wind-up, no rest.' }),
    capfull: enemy('Capfull', '5 HP. Runs from you, catch it for loot', { hp: 5, dmg: [0, 0], range: 1, charge: 1, rest: 1, kind: 'passive', aggro: 7, every: 2, flees: true, implemented: false, note: 'Not in the builder: its loot table is server side.' }),
    jackalot_roam: enemy('Sir Jackalot (roaming)', 'The final boss loose on a normal floor, lines up broad spear thrusts', { hp: 0, dmg: [0, 0], range: 1, charge: 1, rest: 1, kind: 'passive', aggro: 7, every: 2, flees: true, implemented: false, note: 'Not in the builder.' })
  };

  var OBJECTS = {
    pot: { name: 'Pot', short: 'Smash it for 0 Energy. Can hold loot', implemented: true, note: 'Smashing costs 0 Energy and takes the turn (seen in real runs). Drop roll (assumed, the loot table is server side): 5 percent Pot mimic, then 40 percent treasure, 25 percent small energy orb, 35 percent nothing.' },
    crate: { name: 'Crate', short: 'Smash it for 0 Energy. Can hold loot', implemented: true, note: 'Smashing costs 0 Energy and takes the turn. Drop roll (assumed): 40 percent treasure, 25 percent small energy orb, 35 percent nothing.' },
    corn_stalk: { name: 'Corn stalk', short: 'Break it for Golden Corn', implemented: true, note: 'Breaking it costs 0 Energy, takes the turn and drops one Golden Corn worth 10 on the same tile (seen in real runs).' },
    chest: { name: 'Chest', short: 'Open it for loot', implemented: true, note: 'Opening costs 0 Energy and drops a treasure worth 250 coins (assumed: no chest was opened in the recorded runs).' },
    stairs: { name: 'Stairs down', short: 'Exit to the next floor', implemented: true, note: 'Stepping on the stairs wins the floor at once. You still pay 1 Energy for the step, so at 1 Energy the step kills you first, as in the game.' },
    fountain: { name: 'Fountain', short: 'Restores 10 Energy', implemented: true, note: 'Once per floor, when you step into it (+10 seen in real runs).' },
    portal: { name: 'Portal', short: 'Teleports you for coins: 10 the first time, more each use', implemented: false, note: 'Not in the builder.' }
  };
  var PICKUPS = {
    golden_corn: { name: 'Golden Corn', short: 'Step on it to collect. Drops disappear after 20 turns', value: 10, implemented: true, note: 'Placed corn never despawns; corn that drops out of a stalk despawns after 20 turns (seen in real runs).' },
    small_energy_orb: { name: 'Small energy orb', short: 'Step on it to restore 10 Energy', value: 10, implemented: true, note: 'Real drops gave 4 to 16, most often 10; the value grows with the floor.' },
    large_energy_orb: { name: 'Large energy orb', short: 'Step on it to restore 16 Energy', value: 16, implemented: true, note: 'Real drops gave 9 to 24, most often 16; the value grows with the floor.' },
    treasure: { name: 'Treasure', short: 'Step on it to collect coins', value: [10, 40], implemented: true, note: 'Worth 10 to 40 coins, rolled with the floor seed. Real drops gave 8 to 60 and grow with the floor.' },
    item: { name: 'Item', short: 'Step on it to pick up the item', implemented: true, note: 'Needs an item key from RULES.ITEMS.' },
    marble: { name: 'Marble', short: 'Step on it to collect', implemented: false, note: 'Not in the builder.' }
  };
  var TRAPS = {
    spike: { name: 'Spikes', short: 'They rise on alternating turns and hit whoever stands here', dmg: [7, 8], implemented: true, note: 'Up after odd numbered presses (state.turn odd). 7-8 Energy, the values seen in real runs.' },
    arrow: { name: 'Arrow trap', short: 'Fires an arrow along its line every 3 turns', dmg: [8, 10], every: 3, implemented: true, note: 'Sits in a wall or on the floor and blocks its own tile. The arrow flies from the next tile until a wall or a pot, 8-10 Energy if you are on the line (values seen in real runs). Firing every 3 turns is assumed. cues() shows the line one turn before it fires.' }
  };
  var ITEMS = {
    single_shot: { name: 'Single Shot', short: '25 damage to the first enemy in a line, takes your turn', dmg: 25, range: 5, directional: true, implemented: true, note: 'Range is your vision: 5 tiles with 40 or more Energy, 4 from 15, 3 below that. Stops at walls and at the first enemy. A ghost or a shielded Frog egg cluster blocks it without damage.' },
    piercing_shot: { name: 'Piercing Shot', short: '25 damage to up to three enemies on a line, takes your turn', dmg: 25, range: 5, directional: true, implemented: true, note: 'Range is your vision: 5 tiles with 40 or more Energy, 4 from 15, 3 below that. Stops at walls.' },
    pogo_stick: { name: 'Pogo Stick', short: 'Jump over the tile in front of you onto the one behind it, takes your turn', cost: 1, directional: true, implemented: true, note: 'Jumps over walls, enemies and pots. The landing tile must be free floor. Costs 1 Energy like a step (seen in real runs). The game also allows any tile within 3; here it is the tile two steps away.' },
    bomb: { name: 'Bomb', short: 'Adjacent. 30 dmg 3x3 in 3 turns (hits you)', dmg: 30, timer: 3, directional: true, implemented: true, note: 'Placed on the free tile in the chosen direction (the game also allows diagonals). Explodes after 3 turns; you take 30 too if you stand in the 3x3.' },
    chain_shot: { name: 'Chain Shot', short: '35 damage in a line, a kill gives a second shot', implemented: false },
    chain_hook: { name: 'Chain Hook', short: 'Yank an enemy to you and stun it', implemented: false },
    shock_grenade: { name: 'Shock Grenade', short: 'Stun 5x5 for 2 turns', implemented: false },
    escape_rope: { name: 'Escape Rope', short: 'Leave the floor at once', implemented: false },
    magnet: { name: 'Magnet', short: 'Collect all drops within a 6x6 radius', implemented: false },
    pocket_portal: { name: 'Pocket Portal', short: 'Teleport to a random room', implemented: false },
    talisman: { name: 'Talisman', short: 'Catches a ghost, 3 charges', implemented: false },
    switcher: { name: 'Switcher', short: 'Swap places with a visible enemy', implemented: false },
    decoy: { name: 'Decoy', short: 'Enemies chase it for 8 turns', implemented: false },
    midas_touch: { name: 'Midas Touch', short: 'Your next hit turns an enemy into a statue', implemented: false },
    sticky_bomb: { name: 'Sticky Bomb', short: '50 (+30 splash) in 2 turns', implemented: false }
  };
  var WEATHER = {
    blizzard: { name: 'Blizzard', short: 'Drops spawn frozen and a hit gives you Frostbite: attacks cost 2 Energy for 5 turns', implemented: true, note: 'Frozen drops never thaw by themselves (seen in real runs): bump them to crack the ice, 0 Energy, takes the turn. Pickups placed by the builder start unfrozen. Frostbite lasting 5 turns is assumed; smashing stays free under Frostbite.' },
    heatwave: { name: 'Heatwave', short: 'Mirage: wind-ups still show their zones but their timing is unreliable', implemented: true, note: 'Every wind-up lasts its listed length plus or minus 1 (never below 1). cues() still returns the zones; the UI should show enemy.turns as "?".' },
    storm: { name: 'Storm', short: 'Every 4 turns the storm marks your tile, lightning hits it for 25 next turn', implemented: true, note: 'The mark is a cue of kind target with enemyId storm. The 4 turn cadence is assumed; the 25 is from the game.' },
    gale: { name: 'Gale', short: 'Every 4 turns a gust pushes you and every enemy one tile downwind', implemented: true, note: 'The 4 turn cadence and the wind direction (rolled once per floor) are assumed. Rooted enemies and blocked tiles do not move.' },
    miasma: { name: 'Miasma', short: 'Every enemy hit poisons you: 1 Energy per turn for 5 turns', implemented: true, note: 'Poison ticks at the start of the trap phase.' }
  };
  var TALENTS = {
    divine_shield: { name: 'Divine Shield', short: '15 percent chance to block an enemy hit', implemented: true, note: 'Chance, not a reduction. Does not work on traps.' },
    armor_plating: { name: 'Armor Plating', short: 'Takes 15 percent less damage from everything', implemented: true, note: 'Rounded, minimum 1. Applies to traps too.' },
    sharp_blade: { name: 'Sharp Blade', short: 'Your attacks deal 20 percent more damage', implemented: true },
    vampiric: { name: 'Vampiric', short: 'Every 3rd kill restores 10 Energy', implemented: true, note: 'The 10 is the value seen in real runs.' },
    swift_steps: { name: 'Swift Steps', short: '5 free moves at the start of the floor', implemented: true, note: 'Your first 5 steps cost 0 Energy (state.player.freeMoves counts down). Wait, attacks and items are not steps.' },
    thorns: { name: 'Thorns', short: 'Reflects 10 percent of the damage you take back to the attacker', implemented: true, note: 'Minimum 1, never hurts ghosts.' },
    renewal: { name: 'Renewal', short: '5 Energy at the start of each floor', implemented: false },
    last_stand: { name: 'Last Stand', short: 'Survive one killing blow per floor', implemented: false },
    salvage: { name: 'Salvage', short: 'Smashing breakables restores 1 Energy', implemented: false },
    momentum: { name: 'Momentum', short: 'Every 4th kill gives a free move', implemented: false },
    scout: { name: 'Scout', short: 'Vision +1', implemented: false },
    survival_instinct: { name: 'Survival Instinct', short: '5 free moves when you drop below 10 Energy', implemented: false },
    apex_guard: { name: 'Apex Guard', short: 'First hit from a full HP enemy is reduced by 10 percent', implemented: false },
    cleave: { name: 'Cleave', short: '20 percent of your damage hits neighbours', implemented: false },
    critical_strike: { name: 'Critical Boost', short: 'Crit chance +5 percent', implemented: false },
    merciless: { name: 'Merciless', short: '10 percent more damage to enemies below half HP', implemented: false },
    frenzy: { name: 'Frenzy', short: 'Every 3rd kill boosts damage 7 percent', implemented: false },
    disrupt: { name: 'Disrupt', short: '5 percent chance to stun on hit', implemented: false },
    poison_blade: { name: 'Poison Blade', short: '10 percent chance to poison', implemented: false },
    reach: { name: 'Reach', short: 'The enemy behind your target takes 30 percent', implemented: false },
    corruption: { name: 'Corruption', short: '8 percent chance to turn an enemy against its own', implemented: false },
    menace: { name: 'Menace', short: 'Kills frighten neighbours', implemented: false },
    scavenger: { name: 'Scavenger', short: '10 percent more loot from breakables', implemented: false },
    prospector: { name: 'Prospector', short: '25 percent more items from pots', implemented: false },
    apex_hunter: { name: 'Apex Hunter', short: 'Crit chance +15 percent against full HP enemies', implemented: false },
    berserker: { name: 'Berserker', short: '25 percent more damage below 30 Energy', implemented: false },
    heavy_hitter: { name: 'Heavy Hitter', short: '10 percent more damage, each strike costs 1 Energy', implemented: false },
    greed: { name: 'Greed', short: 'Treasure x1.2, 40 percent more damage taken', implemented: false },
    glass_cannon: { name: 'Glass Cannon', short: 'Damage x1.3, max Energy capped at 70', implemented: false }
  };
  var HERO = { energy: 100, maxEnergy: 100, atk: 20, maxTalents: 3, note: 'Move 1 Energy, Wait 1, attack 0, smash 0, item 0 (Pogo Stick 1). Frostbite makes attacks cost 2; smashes stay free. All seen in real runs.' };
  var LIMITS = { minW: 8, maxW: 18, minH: 6, maxH: 11, defaultW: 14, defaultH: 9, maxEnemies: 30, maxName: 40, maxEnergy: 999, maxAtk: 200, despawn: 20, thaw: 0 }; // thaw 0: frozen drops do not thaw by themselves
  var RULES = { ENEMIES: ENEMIES, OBJECTS: OBJECTS, PICKUPS: PICKUPS, TRAPS: TRAPS, ITEMS: ITEMS, WEATHER: WEATHER, TALENTS: TALENTS, HERO: HERO, LIMITS: LIMITS };

  var SOLID_OBJECTS = { pot: true, crate: true, corn_stalk: true, chest: true, portal: true };
  var SMASH_VERB = { pot: 'Smash', crate: 'Smash', corn_stalk: 'Break', chest: 'Open' };

  /* ===================================================================================================
   * 3. Grid lookups on a state
   * =================================================================================================== */
  function inb(st, x, y) { return x >= 0 && y >= 0 && x < st.w && y < st.h; }
  function isWall(st, x, y) { return !inb(st, x, y) || st.rows[y].charAt(x) === '#'; }
  function enemyAt(st, x, y) { var i; for (i = 0; i < st.enemies.length; i++) if (st.enemies[i].x === x && st.enemies[i].y === y) return st.enemies[i]; return null; }
  function objectAt(st, x, y) { var i; for (i = 0; i < st.objects.length; i++) if (st.objects[i].x === x && st.objects[i].y === y) return st.objects[i]; return null; }
  function pickupAt(st, x, y) { var i; for (i = 0; i < st.pickups.length; i++) if (st.pickups[i].x === x && st.pickups[i].y === y) return st.pickups[i]; return null; }
  function trapAt(st, x, y) { var i; for (i = 0; i < st.traps.length; i++) if (st.traps[i].x === x && st.traps[i].y === y) return st.traps[i]; return null; }
  function solidAt(st, x, y) { // things nobody walks through: walls, pots and friends, arrow trap stones, frozen drops
    var o, t, p;
    if (isWall(st, x, y)) return true;
    o = objectAt(st, x, y); if (o && SOLID_OBJECTS[o.type]) return true;
    t = trapAt(st, x, y); if (t && t.type === 'arrow') return true;
    p = pickupAt(st, x, y); if (p && p.frozen > 0) return true;
    return false;
  }
  function freeForEnemy(st, x, y, e) { // a tile an enemy may step onto
    var cfg = ENEMIES[e.type];
    if (isWall(st, x, y)) return false;
    if (st.player.x === x && st.player.y === y) return false;
    if (enemyAt(st, x, y)) return false;
    if (cfg.invincible) return true; // ghosts float over pots and drops
    return !solidAt(st, x, y);
  }
  function lineTiles(st, x, y, dir, range) { // straight line from (x,y) excluding it, stops at walls
    var d = DIRS[dir], out = [], n, cx = x + d.dx, cy = y + d.dy;
    for (n = 0; n < range && !isWall(st, cx, cy); n++) { out.push({ x: cx, y: cy }); cx += d.dx; cy += d.dy; }
    return out;
  }
  function n4(st, x, y) { var out = [], i, D; for (i = 0; i < 4; i++) { D = DIRS[DIR_IDS[i]]; if (!isWall(st, x + D.dx, y + D.dy)) out.push({ x: x + D.dx, y: y + D.dy }); } return out; }
  function ring8(st, x, y, withCenter) { var out = [], dx, dy; for (dy = -1; dy <= 1; dy++) for (dx = -1; dx <= 1; dx++) { if (!dx && !dy && !withCenter) continue; if (!isWall(st, x + dx, y + dy)) out.push({ x: x + dx, y: y + dy }); } return out; }
  function inZone(zone, x, y) { var i; for (i = 0; i < zone.length; i++) if (zone[i].x === x && zone[i].y === y) return true; return false; }
  function dirTo(ax, ay, bx, by) { var dx = bx - ax, dy = by - ay; if (Math.abs(dx) >= Math.abs(dy)) return dx >= 0 ? 'right' : 'left'; return dy > 0 ? 'down' : 'up'; }
  function lineDirTo(ax, ay, bx, by) { if (ax === bx && ay === by) return null; if (ax === bx) return by > ay ? 'down' : 'up'; if (ay === by) return bx > ax ? 'right' : 'left'; return null; }
  function ename(e) { return ENEMIES[e.type] ? ENEMIES[e.type].name : e.type; }
  function nextId(st, prefix) { st.nextId += 1; return prefix + st.nextId; }
  function hasTalent(st, key) { return has(st.player.talents, key); }
  function pushEv(ev, e) { ev.push(e); return e; }

  /* ===================================================================================================
   * 4. validate(spec)
   * =================================================================================================== */
  function validate(spec) {
    var errors = [], rows, w, h, y, x, occ = {}, stairs = 0, hero, i, seen = {};
    function occupy(kind, o) {
      var k;
      if (!o || !isInt(o.x) || !isInt(o.y) || o.x < 0 || o.y < 0 || o.x >= w || o.y >= h) { errors.push(kind + ' at (' + (o && o.x) + ',' + (o && o.y) + ') is outside the grid.'); return false; }
      k = o.x + ',' + o.y;
      if (occ[k]) { errors.push(kind + ' at (' + o.x + ',' + o.y + ') shares a tile with ' + occ[k] + '.'); return false; }
      occ[k] = kind;
      return true;
    }
    if (!spec || typeof spec !== 'object') return { ok: false, errors: ['The floor is not an object.'] };
    if (spec.v !== 1) errors.push('Unknown floor version.');
    w = spec.w; h = spec.h;
    if (!isInt(w) || w < LIMITS.minW || w > LIMITS.maxW) errors.push('Width must be ' + LIMITS.minW + ' to ' + LIMITS.maxW + '.');
    if (!isInt(h) || h < LIMITS.minH || h > LIMITS.maxH) errors.push('Height must be ' + LIMITS.minH + ' to ' + LIMITS.maxH + '.');
    if (errors.length) return { ok: false, errors: errors };
    if (typeof spec.tiles !== 'string') { errors.push('Tiles must be a string.'); return { ok: false, errors: errors }; }
    rows = spec.tiles.split('\n');
    if (rows.length !== h) errors.push('Tiles must have ' + h + ' rows.');
    for (y = 0; y < rows.length; y++) {
      if (rows[y].length !== w) { errors.push('Tile row ' + y + ' must have ' + w + ' characters.'); continue; }
      for (x = 0; x < w; x++) if (rows[y].charAt(x) !== '#' && rows[y].charAt(x) !== '.') { errors.push('Tile row ' + y + ' has a character that is not # or . at ' + x + '.'); break; }
    }
    if (errors.length) return { ok: false, errors: errors };
    function floorTile(x, y) { return x >= 0 && y >= 0 && x < w && y < h && rows[y].charAt(x) === '.'; }
    if (spec.name != null && (typeof spec.name !== 'string' || spec.name.length > LIMITS.maxName)) errors.push('Name must be text of at most ' + LIMITS.maxName + ' characters.');
    if (spec.weather != null && !(WEATHER[spec.weather] && WEATHER[spec.weather].implemented)) errors.push('Unknown weather: ' + spec.weather + '.');
    if (!spec.start || !isInt(spec.start.x) || !isInt(spec.start.y) || !floorTile(spec.start.x, spec.start.y)) errors.push('The hero start must be on a floor tile.');
    else occ[spec.start.x + ',' + spec.start.y] = 'the hero start';
    ['enemies', 'objects', 'pickups', 'traps'].forEach(function (key) { if (spec[key] != null && !Array.isArray(spec[key])) errors.push(key + ' must be a list.'); });
    if (errors.length) return { ok: false, errors: errors };
    (spec.enemies || []).forEach(function (e) {
      var cfg = e && ENEMIES[e.type];
      if (!cfg || !cfg.implemented) { errors.push('Unknown enemy type: ' + (e && e.type) + '.'); return; }
      if (occupy(cfg.name, e) && !floorTile(e.x, e.y)) errors.push(cfg.name + ' at (' + e.x + ',' + e.y + ') must be on a floor tile.');
    });
    if ((spec.enemies || []).length > LIMITS.maxEnemies) errors.push('At most ' + LIMITS.maxEnemies + ' enemies.');
    (spec.objects || []).forEach(function (o) {
      var cfg = o && OBJECTS[o.type];
      if (!cfg || !cfg.implemented) { errors.push('Unknown object type: ' + (o && o.type) + '.'); return; }
      if (o.type === 'stairs') stairs += 1;
      if (occupy(cfg.name, o) && !floorTile(o.x, o.y)) errors.push(cfg.name + ' at (' + o.x + ',' + o.y + ') must be on a floor tile.');
    });
    if (stairs !== 1) errors.push(stairs === 0 ? 'The floor needs one Stairs down.' : 'Only one Stairs down is allowed.');
    (spec.pickups || []).forEach(function (p) {
      var cfg = p && PICKUPS[p.type];
      if (!cfg || !cfg.implemented) { errors.push('Unknown pickup type: ' + (p && p.type) + '.'); return; }
      if (p.type === 'item' && !(ITEMS[p.item] && ITEMS[p.item].implemented)) errors.push('Unknown item on the floor: ' + p.item + '.');
      if (occupy(cfg.name, p) && !floorTile(p.x, p.y)) errors.push(cfg.name + ' at (' + p.x + ',' + p.y + ') must be on a floor tile.');
    });
    (spec.traps || []).forEach(function (t) {
      var cfg = t && TRAPS[t.type];
      if (!cfg || !cfg.implemented) { errors.push('Unknown trap type: ' + (t && t.type) + '.'); return; }
      if (t.type === 'arrow' && !DIRS[t.dir]) errors.push('Arrow trap at (' + t.x + ',' + t.y + ') needs a direction.');
      if (occupy(cfg.name, t) && t.type === 'spike' && !floorTile(t.x, t.y)) errors.push('Spikes at (' + t.x + ',' + t.y + ') must be on a floor tile.');
    });
    hero = spec.hero || {};
    if (hero.energy != null && (!isInt(hero.energy) || hero.energy < 1 || hero.energy > LIMITS.maxEnergy)) errors.push('Hero Energy must be 1 to ' + LIMITS.maxEnergy + '.');
    if (hero.maxEnergy != null && (!isInt(hero.maxEnergy) || hero.maxEnergy < 1 || hero.maxEnergy > LIMITS.maxEnergy)) errors.push('Hero max Energy must be 1 to ' + LIMITS.maxEnergy + '.');
    if (hero.energy != null && hero.maxEnergy != null && hero.energy > hero.maxEnergy) errors.push('Hero Energy cannot exceed max Energy.');
    if (hero.atk != null && (!isInt(hero.atk) || hero.atk < 1 || hero.atk > LIMITS.maxAtk)) errors.push('Hero ATK must be 1 to ' + LIMITS.maxAtk + '.');
    if (hero.items != null) {
      if (!Array.isArray(hero.items)) errors.push('Hero items must be a list.');
      else hero.items.forEach(function (k) { if (!(ITEMS[k] && ITEMS[k].implemented)) errors.push('Unknown item: ' + k + '.'); });
    }
    if (hero.talents != null) {
      if (!Array.isArray(hero.talents)) errors.push('Hero talents must be a list.');
      else {
        if (hero.talents.length > HERO.maxTalents) errors.push('At most ' + HERO.maxTalents + ' talents.');
        for (i = 0; i < hero.talents.length; i++) {
          if (!(TALENTS[hero.talents[i]] && TALENTS[hero.talents[i]].implemented)) errors.push('Unknown talent: ' + hero.talents[i] + '.');
          else if (seen[hero.talents[i]]) errors.push('Talent listed twice: ' + hero.talents[i] + '.');
          seen[hero.talents[i]] = true;
        }
      }
    }
    return { ok: errors.length === 0, errors: errors };
  }

  /* ===================================================================================================
   * 5. encode(spec) / decode(str): compact JSON with code tables, run length tiles, base64url
   * =================================================================================================== */
  var ENEMY_CODES = ['smallslime', 'mediumslime', 'bat', 'skelechump', 'skelesoldier', 'dragma_bat', 'dragma_skelechump', 'dragma_skelesoldier', 'ghost1', 'ghost2', 'ghost3', 'mimic', 'potmimick', 'skelearcher', 'boomcap', 'lobcap', 'whipweed', 'megawhipweed', 'frogglet', 'frogspawn', 'croaker', 'capfull', 'jackalot_roam'];
  var OBJECT_CODES = ['pot', 'crate', 'corn_stalk', 'chest', 'stairs', 'fountain', 'portal'];
  var PICKUP_CODES = ['golden_corn', 'small_energy_orb', 'large_energy_orb', 'treasure', 'item', 'marble'];
  var TRAP_CODES = ['spike', 'arrow'];
  var WEATHER_CODES = [null, 'blizzard', 'heatwave', 'storm', 'gale', 'miasma'];
  var ITEM_CODES = ['single_shot', 'pogo_stick', 'bomb', 'piercing_shot', 'chain_shot', 'chain_hook', 'shock_grenade', 'escape_rope', 'magnet', 'pocket_portal', 'talisman', 'switcher', 'decoy', 'midas_touch', 'sticky_bomb'];
  var TALENT_CODES = ['divine_shield', 'armor_plating', 'sharp_blade', 'vampiric', 'swift_steps', 'thorns', 'renewal', 'last_stand', 'salvage', 'momentum', 'scout', 'survival_instinct', 'apex_guard', 'cleave', 'critical_strike', 'merciless', 'frenzy', 'disrupt', 'poison_blade', 'reach', 'corruption', 'menace', 'scavenger', 'prospector', 'apex_hunter', 'berserker', 'heavy_hitter', 'greed', 'glass_cannon'];
  function code(list, v) { var i = list.indexOf(v); return i < 0 ? -1 : i; }
  function uncode(list, i) { return isInt(i) && i >= 0 && i < list.length ? list[i] : null; }
  function rleTiles(tiles) {
    var s = String(tiles).replace(/\n/g, ''), out = '', i, c = '', n = 0;
    for (i = 0; i <= s.length; i++) {
      if (i < s.length && s.charAt(i) === c) { n++; continue; }
      if (n) out += c + n;
      c = s.charAt(i); n = 1;
    }
    return out;
  }
  function unrleTiles(s, w, h) {
    var out = '', re = /([#.])(\d+)/g, m, i, rows = [], y, n;
    if (!isInt(w) || !isInt(h) || w < LIMITS.minW || w > LIMITS.maxW || h < LIMITS.minH || h > LIMITS.maxH) return null;
    while ((m = re.exec(String(s)))) { n = +m[2]; if (out.length + n > w * h) return null; for (i = 0; i < n; i++) out += m[1]; }
    if (out.length !== w * h) return null;
    for (y = 0; y < h; y++) rows.push(out.substr(y * w, w));
    return rows.join('\n');
  }
  function encode(spec) {
    var hero = spec.hero || {}, c = {
      v: 1, w: spec.w, h: spec.h, t: rleTiles(spec.tiles), s: [spec.start.x, spec.start.y],
      e: (spec.enemies || []).map(function (e) { return [code(ENEMY_CODES, e.type), e.x, e.y]; }),
      o: (spec.objects || []).map(function (o) { return [code(OBJECT_CODES, o.type), o.x, o.y]; }),
      p: (spec.pickups || []).map(function (p) { return p.type === 'item' ? [code(PICKUP_CODES, p.type), p.x, p.y, code(ITEM_CODES, p.item)] : [code(PICKUP_CODES, p.type), p.x, p.y]; }),
      r: (spec.traps || []).map(function (t) { return t.type === 'arrow' ? [code(TRAP_CODES, t.type), t.x, t.y, code(DIR_IDS, t.dir)] : [code(TRAP_CODES, t.type), t.x, t.y]; }),
      k: [hero.energy != null ? hero.energy : HERO.energy, hero.maxEnergy != null ? hero.maxEnergy : HERO.maxEnergy, hero.atk != null ? hero.atk : HERO.atk,
        (hero.items || []).map(function (k) { return code(ITEM_CODES, k); }), (hero.talents || []).map(function (k) { return code(TALENT_CODES, k); })]
    };
    if (spec.name) c.n = String(spec.name).slice(0, LIMITS.maxName);
    if (spec.weather) c.we = code(WEATHER_CODES, spec.weather);
    return b64Encode(utf8Bytes(JSON.stringify(c)));
  }
  function decode(str) {
    var bytes, c, spec;
    try {
      if (typeof str !== 'string' || !str) return null;
      bytes = b64Decode(str); if (!bytes) return null;
      c = JSON.parse(utf8Str(bytes));
      if (!c || c.v !== 1 || !isInt(c.w) || !isInt(c.h)) return null;
      spec = {
        v: 1, w: c.w, h: c.h, name: typeof c.n === 'string' ? c.n : '', weather: c.we != null ? uncode(WEATHER_CODES, c.we) : null,
        tiles: unrleTiles(c.t, c.w, c.h), start: { x: c.s[0], y: c.s[1] },
        enemies: (c.e || []).map(function (a) { return { type: uncode(ENEMY_CODES, a[0]), x: a[1], y: a[2] }; }),
        objects: (c.o || []).map(function (a) { return { type: uncode(OBJECT_CODES, a[0]), x: a[1], y: a[2] }; }),
        pickups: (c.p || []).map(function (a) { var p = { type: uncode(PICKUP_CODES, a[0]), x: a[1], y: a[2] }; if (a.length > 3) p.item = uncode(ITEM_CODES, a[3]); return p; }),
        traps: (c.r || []).map(function (a) { var t = { type: uncode(TRAP_CODES, a[0]), x: a[1], y: a[2] }; if (a.length > 3) t.dir = uncode(DIR_IDS, a[3]); return t; }),
        hero: { energy: c.k[0], maxEnergy: c.k[1], atk: c.k[2], items: (c.k[3] || []).map(function (i) { return uncode(ITEM_CODES, i); }), talents: (c.k[4] || []).map(function (i) { return uncode(TALENT_CODES, i); }) }
      };
      if (spec.tiles === null) return null;
      return spec;
    } catch (err) { return null; }
  }

  /* ===================================================================================================
   * 6. newGame(spec)
   * =================================================================================================== */
  function newGame(spec) {
    var v = validate(spec), hero, st, seed;
    if (!v.ok) throw new Error('Invalid floor: ' + v.errors.join(' '));
    hero = spec.hero || {};
    seed = hash32(encode(spec));
    st = {
      v: 1, name: spec.name || 'Untitled floor', w: spec.w, h: spec.h, tiles: spec.tiles, rows: spec.tiles.split('\n'),
      turn: 0, status: 'playing', weather: spec.weather || null, seed: seed, rng: seed | 0, wind: null,
      player: {
        x: spec.start.x, y: spec.start.y,
        energy: hero.energy != null ? hero.energy : HERO.energy, maxEnergy: hero.maxEnergy != null ? hero.maxEnergy : HERO.maxEnergy,
        atk: hero.atk != null ? hero.atk : HERO.atk, items: (hero.items || []).slice(), talents: (hero.talents || []).slice(),
        corn: 0, coins: 0, poison: 0, frostbite: 0, freeMoves: 0
      },
      enemies: [], objects: [], pickups: [], traps: [], bombs: [], strikes: [], log: [], result: null, kills: 0, vamp: 0, nextId: 0
    };
    if (st.player.maxEnergy < st.player.energy) st.player.maxEnergy = st.player.energy;
    if (hasTalent(st, 'swift_steps')) st.player.freeMoves = 5;
    (spec.enemies || []).forEach(function (e) {
      var cfg = ENEMIES[e.type];
      st.enemies.push({ id: nextId(st, 'e'), type: e.type, x: e.x, y: e.y, hp: cfg.hp, maxHp: cfg.hp, phase: 'idle', turns: 0, target: null, dir: null, shield: 0, invincible: !!cfg.invincible, zone: [], clock: 0, spawns: cfg.kind === 'spawner' ? 4 : 0, flee: 0, revealed: !cfg.ambush, thrown: null });
    });
    (spec.objects || []).forEach(function (o) { st.objects.push({ id: nextId(st, 'o'), type: o.type, x: o.x, y: o.y, used: false }); });
    (spec.pickups || []).forEach(function (p) { st.pickups.push(makePickup(st, p.type, p.x, p.y, p.item, 0, 0)); });
    (spec.traps || []).forEach(function (t) { st.traps.push({ id: nextId(st, 't'), type: t.type, x: t.x, y: t.y, dir: t.type === 'arrow' ? t.dir : null, up: false, timer: t.type === 'arrow' ? TRAPS.arrow.every : 0 }); });
    if (st.weather === 'gale') st.wind = rngPick(st, DIR_IDS);
    updateShields(st);
    st.log.push({ turn: 0, text: 'Reach the stairs. A move costs 1 Energy, attacks and smashes cost 0.' + (st.weather ? ' ' + WEATHER[st.weather].name + ': ' + WEATHER[st.weather].short + '.' : '') });
    return st;
  }
  function makePickup(st, type, x, y, item, despawn, frozen) {
    var value = PICKUPS[type] && PICKUPS[type].value;
    if (type === 'treasure') value = rngInt(st, PICKUPS.treasure.value[0], PICKUPS.treasure.value[1]);
    return { id: nextId(st, 'p'), type: type, x: x, y: y, item: type === 'item' ? item : null, value: typeof value === 'number' ? value : 0, despawn: despawn || 0, frozen: frozen || 0, fresh: false };
  }
  function updateShields(st) {
    var n = 0, i;
    for (i = 0; i < st.enemies.length; i++) if (st.enemies[i].type === 'frogglet') n++;
    for (i = 0; i < st.enemies.length; i++) st.enemies[i].shield = st.enemies[i].type === 'frogspawn' ? n : 0;
  }

  /* ===================================================================================================
   * 7. actions(state)
   * =================================================================================================== */
  function pickupName(p) { return p.type === 'item' ? (ITEMS[p.item] ? ITEMS[p.item].name : 'Item') : PICKUPS[p.type].name; }
  function itemDirs(st, key) { // directions in which the item can be used right now
    var p = st.player, out = [], i, d, D, x, y, x2, y2;
    for (i = 0; i < 4; i++) {
      d = DIR_IDS[i]; D = DIRS[d]; x = p.x + D.dx; y = p.y + D.dy; x2 = p.x + 2 * D.dx; y2 = p.y + 2 * D.dy;
      if (key === 'pogo_stick') { if (!solidAt(st, x2, y2) && !enemyAt(st, x2, y2) && inb(st, x2, y2)) out.push(d); }
      else if (key === 'bomb') { if (!solidAt(st, x, y) && !enemyAt(st, x, y) && !(objectAt(st, x, y))) out.push(d); }
      else if (!isWall(st, x, y)) out.push(d);
    }
    return out;
  }
  function actions(st) {
    var out = [], p = st.player, playing = st.status === 'playing', i, d, D, x, y, a, e, o, pk, t, cfg, seen = {};
    for (i = 0; i < 4; i++) {
      d = DIR_IDS[i]; D = DIRS[d]; x = p.x + D.dx; y = p.y + D.dy;
      a = { id: d, dir: d, kind: 'move', label: 'Step ' + D.arrow, target: { x: x, y: y }, enabled: playing, why: '', sub: p.freeMoves > 0 ? 'Free move' : '', cost: p.freeMoves > 0 ? 0 : 1 };
      if (!playing) { a.enabled = false; a.why = 'The run is over.'; out.push(a); continue; }
      e = enemyAt(st, x, y); o = objectAt(st, x, y); pk = pickupAt(st, x, y); t = trapAt(st, x, y);
      if (isWall(st, x, y)) { a.kind = 'blocked'; a.enabled = false; a.why = 'That is a wall.'; a.label = 'Wall ' + D.arrow; a.cost = 0; }
      else if (e && e.invincible) { a.kind = 'blocked'; a.enabled = false; a.why = 'A ghost blocks that tile. Nothing can be done into it.'; a.label = 'Ghost ' + D.arrow; a.cost = 0; }
      else if (e) {
        cfg = ENEMIES[e.type];
        a.kind = 'attack'; a.label = 'Attack ' + D.arrow; a.cost = p.frostbite > 0 ? 2 : 0;
        a.sub = cfg.name + ' ' + e.hp + '/' + e.maxHp + ' HP';
        if (e.shield > 0) a.sub += ', shielded by ' + e.shield + ' Blue frog' + (e.shield === 1 ? '' : 's');
        else if (e.hp <= heroDamage(st)) a.sub += ', one hit kills it';
        a.why = a.sub;
      }
      else if (o && SMASH_VERB[o.type]) { a.kind = 'break'; a.label = SMASH_VERB[o.type] + ' ' + D.arrow; a.sub = OBJECTS[o.type].name; a.cost = 0; }
      else if (t && t.type === 'arrow') { a.kind = 'blocked'; a.enabled = false; a.why = 'The arrow trap stone blocks that tile.'; a.label = 'Trap ' + D.arrow; a.cost = 0; }
      else if (pk && pk.frozen > 0) { a.kind = 'break'; a.label = 'Crack ' + D.arrow; a.sub = 'Frozen ' + pickupName(pk) + ', bump it to crack the ice'; a.cost = 0; }
      else if (o && o.type === 'stairs') { a.sub = 'Stairs down: leave the floor'; }
      else if (o && o.type === 'fountain') { a.sub = o.used ? 'Fountain, already used' : 'Fountain: +10 Energy'; }
      else if (pk) { a.kind = 'pickup'; a.sub = pickupName(pk); }
      else if (t && t.type === 'spike') { a.sub = ((st.turn + 1) % 2 === 1) ? 'Spikes rise this turn' : 'Spikes stay down this turn'; }
      out.push(a);
    }
    out.push({ id: 'pass', dir: null, kind: 'pass', label: 'Wait', target: null, enabled: playing, why: playing ? '' : 'The run is over.', sub: '1 Energy', cost: 1 });
    for (i = 0; i < p.items.length; i++) {
      if (seen[p.items[i]]) continue;
      seen[p.items[i]] = true;
      cfg = ITEMS[p.items[i]];
      if (!cfg || !cfg.implemented) continue;
      a = { id: 'item:' + p.items[i], dir: null, kind: 'item', label: cfg.name, target: null, enabled: playing, why: '', sub: cfg.short, cost: cfg.cost || 0, item: p.items[i], directional: !!cfg.directional, dirs: [] };
      if (playing) { a.dirs = itemDirs(st, p.items[i]); if (!a.dirs.length) { a.enabled = false; a.why = 'No direction works here.'; } }
      else a.why = 'The run is over.';
      out.push(a);
    }
    return out;
  }

  /* ===================================================================================================
   * 8. Damage, kills, drops, pickups
   * =================================================================================================== */
  function heroDamage(st) { var d = st.player.atk; if (hasTalent(st, 'sharp_blade')) d = Math.round(d * 1.2); return d; }
  function endRun(st, ev, status, cause) {
    st.status = status;
    st.result = { turns: st.turn, corn: st.player.corn, coins: st.player.coins, energy: st.player.energy, kills: st.kills, cause: cause || null };
    if (status === 'won') pushEv(ev, { t: 'win', x: st.player.x, y: st.player.y, text: 'You reach the stairs with ' + st.player.energy + ' Energy left.' });
    else pushEv(ev, { t: 'dead', x: st.player.x, y: st.player.y, text: 'Run over on turn ' + st.turn + ': ' + cause + '.' });
  }
  function aAn(name) { return (/^[aeiou]/i.test(name) ? 'an ' : 'a ') + name; }
  /* The hero takes damage. cause: short phrase for result.cause ("an Orange slime", "spikes"), e: attacking enemy or
   * null (traps, bombs, weather), evType: event type, prefix: log text before the number. */
  function hurt(st, ev, amount, cause, e, evType, prefix) {
    var p = st.player, reflect, cfg;
    if (st.status !== 'playing') return 0;
    if (hasTalent(st, 'armor_plating')) amount = Math.max(1, Math.round(amount * 0.85));
    if (e && hasTalent(st, 'divine_shield') && rngNext(st) < 0.15) {
      pushEv(ev, { t: 'blocked_hit', x: p.x, y: p.y, enemyId: e.id, dmg: 0, text: 'Divine Shield blocks the ' + ename(e) + '.' });
      return 0;
    }
    p.energy -= amount;
    pushEv(ev, { t: evType || 'hit', x: p.x, y: p.y, enemyId: e ? e.id : null, dmg: amount, text: (prefix || (e ? ename(e) + ' hits you for ' : cause + ' hits you for ')) + amount + '.' });
    if (e) {
      cfg = ENEMIES[e.type];
      if (st.weather === 'miasma') p.poison = 5;
      if (st.weather === 'blizzard') p.frostbite = 5;
      if (hasTalent(st, 'thorns') && !cfg.invincible && e.hp > 0) {
        reflect = Math.max(1, Math.round(amount * 0.1));
        e.hp -= reflect;
        pushEv(ev, { t: 'attack', x: e.x, y: e.y, enemyId: e.id, dmg: reflect, text: 'Thorns: the ' + ename(e) + ' takes ' + reflect + '.' });
        if (e.hp <= 0) killEnemy(st, ev, e, true);
      }
    }
    if (p.energy <= 0) { p.energy = 0; endRun(st, ev, 'dead', cause); }
    return amount;
  }
  function removeEnemy(st, e) { var i = st.enemies.indexOf(e); if (i >= 0) st.enemies.splice(i, 1); }
  function killEnemy(st, ev, e, byHero) {
    var text = 'You kill the ' + ename(e) + '.';
    removeEnemy(st, e);
    if (byHero) {
      st.kills += 1;
      if (hasTalent(st, 'vampiric')) {
        st.vamp += 1;
        if (st.vamp % 3 === 0) { st.player.energy = Math.min(st.player.maxEnergy, st.player.energy + 10); text += ' Vampiric: +10 Energy.'; }
      }
    }
    pushEv(ev, { t: 'kill', x: e.x, y: e.y, enemyId: e.id, text: text });
    updateShields(st);
  }
  function damageEnemy(st, ev, e, dmg, src) { // hero side damage (attacks, shots, bombs). Returns true if the enemy died.
    if (e.invincible) { pushEv(ev, { t: 'blocked_hit', x: e.x, y: e.y, enemyId: e.id, dmg: 0, text: 'The ' + ename(e) + ' is invulnerable.' }); return false; }
    if (e.shield > 0) { pushEv(ev, { t: 'blocked_hit', x: e.x, y: e.y, enemyId: e.id, dmg: 0, text: 'The ' + ename(e) + ' is shielded by its frogs.' }); return false; }
    e.revealed = true;
    e.hp -= dmg;
    if (e.hp <= 0) { pushEv(ev, { t: 'attack', x: e.x, y: e.y, enemyId: e.id, dmg: dmg, text: src + ' hits the ' + ename(e) + ' for ' + dmg + '.' }); killEnemy(st, ev, e, true); return true; }
    pushEv(ev, { t: 'attack', x: e.x, y: e.y, enemyId: e.id, dmg: dmg, text: src + ' hits the ' + ename(e) + ' for ' + dmg + ' (' + e.hp + ' HP left).' });
    return false;
  }
  function addDrop(st, ev, type, x, y, item, value) {
    var pk = makePickup(st, type, x, y, item, LIMITS.despawn, st.weather === 'blizzard' ? 1 : 0), what; // frozen 1 = iced until cracked
    if (typeof value === 'number') pk.value = value;
    pk.fresh = true; // its despawn timer starts counting on the next turn, so the state shows the full 20
    st.pickups.push(pk);
    what = type === 'golden_corn' ? 'Golden Corn drops out' : type === 'treasure' ? 'a treasure drop appears' : aAn(pickupName(pk)) + ' appears';
    pushEv(ev, { t: 'drop', x: x, y: y, value: pk.value, text: what.charAt(0).toUpperCase() + what.slice(1) + (pk.frozen ? ', frozen. Bump it to crack the ice.' : '.') });
    return pk;
  }
  function collectHere(st, ev) { // pickups and objects under the hero after a move
    var p = st.player, pk = pickupAt(st, p.x, p.y), o = objectAt(st, p.x, p.y), gain;
    if (pk && pk.frozen <= 0) {
      st.pickups.splice(st.pickups.indexOf(pk), 1);
      if (pk.type === 'golden_corn') { p.corn += pk.value; pushEv(ev, { t: 'pickup', x: p.x, y: p.y, value: pk.value, text: 'You pick up Golden Corn: +' + pk.value + '.' }); }
      else if (pk.type === 'treasure') { p.coins += pk.value; pushEv(ev, { t: 'pickup', x: p.x, y: p.y, value: pk.value, text: 'Treasure: +' + pk.value + ' coins.' }); }
      else if (pk.type === 'item') { p.items.push(pk.item); pushEv(ev, { t: 'pickup', x: p.x, y: p.y, value: 0, text: 'You pick up a ' + pickupName(pk) + '.' }); }
      else { gain = Math.min(pk.value, p.maxEnergy - p.energy); p.energy += gain; pushEv(ev, { t: 'pickup', x: p.x, y: p.y, value: gain, text: pickupName(pk) + ': +' + gain + ' Energy.' }); }
    }
    if (o && o.type === 'fountain' && !o.used) { o.used = true; gain = Math.min(10, p.maxEnergy - p.energy); p.energy += gain; pushEv(ev, { t: 'pickup', x: p.x, y: p.y, value: gain, text: 'The fountain restores ' + gain + ' Energy.' }); }
    if (o && o.type === 'stairs') endRun(st, ev, 'won', null);
  }
  function smash(st, ev, o) {
    var p = st.player, r, m;
    st.objects.splice(st.objects.indexOf(o), 1);
    if (o.type === 'corn_stalk') { pushEv(ev, { t: 'smash', x: o.x, y: o.y, text: 'You break the corn stalk.' }); addDrop(st, ev, 'golden_corn', o.x, o.y, null, PICKUPS.golden_corn.value); return; }
    if (o.type === 'chest') { pushEv(ev, { t: 'smash', x: o.x, y: o.y, text: 'You open the chest.' }); addDrop(st, ev, 'treasure', o.x, o.y, null, 250); return; }
    r = rngNext(st);
    if (o.type === 'pot' && r < 0.05) {
      m = { id: nextId(st, 'e'), type: 'potmimick', x: o.x, y: o.y, hp: ENEMIES.potmimick.hp, maxHp: ENEMIES.potmimick.hp, phase: 'idle', turns: 0, target: null, dir: null, shield: 0, invincible: false, zone: [], clock: 0, spawns: 0, flee: 0, revealed: true, thrown: null };
      st.enemies.push(m);
      pushEv(ev, { t: 'spawn', x: o.x, y: o.y, enemyId: m.id, text: 'The pot was a Pot mimic!' });
      return;
    }
    r = rngNext(st);
    if (r < 0.40) { pushEv(ev, { t: 'smash', x: o.x, y: o.y, text: 'You smash the ' + o.type + '.' }); addDrop(st, ev, 'treasure', o.x, o.y); }
    else if (r < 0.65) { pushEv(ev, { t: 'smash', x: o.x, y: o.y, text: 'You smash the ' + o.type + '.' }); addDrop(st, ev, 'small_energy_orb', o.x, o.y); }
    else pushEv(ev, { t: 'smash', x: o.x, y: o.y, text: 'You smash the ' + o.type + ': nothing inside.' });
  }

  /* ===================================================================================================
   * 9. Hero press
   * =================================================================================================== */
  function heroPress(st, ev, id, opts) { // returns false when the press is refused (no turn passes)
    var p = st.player, d, D, x, y, e, o, pk, key, cfg, dir, t;
    if (id === 'pass') { p.energy -= 1; pushEv(ev, { t: 'pass', x: p.x, y: p.y, text: 'You wait.' }); if (p.energy <= 0) { p.energy = 0; endRun(st, ev, 'dead', 'you ran out of Energy'); } return true; }
    if (id.indexOf('item:') === 0) {
      key = id.slice(5); cfg = ITEMS[key]; dir = opts && opts.dir;
      if (!cfg || !cfg.implemented || !has(p.items, key)) { pushEv(ev, { t: 'blocked', x: p.x, y: p.y, text: 'You do not have that item.' }); return false; }
      if (cfg.directional && !DIRS[dir]) { pushEv(ev, { t: 'blocked', x: p.x, y: p.y, text: cfg.name + ' needs a direction.' }); return false; }
      if (!has(itemDirs(st, key), dir)) { pushEv(ev, { t: 'blocked', x: p.x, y: p.y, text: cfg.name + ' cannot be used ' + DIRS[dir].word + ' from here.' }); return false; }
      p.items.splice(p.items.indexOf(key), 1);
      useItem(st, ev, key, dir);
      return true;
    }
    D = DIRS[id];
    if (!D) { pushEv(ev, { t: 'blocked', x: p.x, y: p.y, text: 'Unknown action.' }); return false; }
    x = p.x + D.dx; y = p.y + D.dy; d = id;
    if (isWall(st, x, y)) { pushEv(ev, { t: 'blocked', x: x, y: y, text: 'That is a wall. You do not move.' }); return false; }
    e = enemyAt(st, x, y);
    if (e && e.invincible) { pushEv(ev, { t: 'blocked', x: x, y: y, enemyId: e.id, text: 'The ' + ename(e) + ' blocks that tile. The game ignores the action.' }); return false; }
    t = trapAt(st, x, y);
    if (t && t.type === 'arrow') { pushEv(ev, { t: 'blocked', x: x, y: y, text: 'The arrow trap stone blocks that tile.' }); return false; }
    if (e) { spendStrike(st, ev); damageEnemy(st, ev, e, heroDamage(st), 'Your attack'); return true; }
    o = objectAt(st, x, y);
    if (o && SMASH_VERB[o.type]) { smash(st, ev, o); return true; } // smashing is free even under Frostbite (real runs)
    pk = pickupAt(st, x, y);
    if (pk && pk.frozen > 0) { pk.frozen = 0; pushEv(ev, { t: 'thaw', x: x, y: y, text: 'You crack the ice around the ' + pickupName(pk) + '.' }); return true; }
    if (p.freeMoves > 0) { p.freeMoves -= 1; pushEv(ev, { t: 'move', x: x, y: y, text: 'You step ' + D.word + ' (free move, ' + p.freeMoves + ' left).' }); }
    else { p.energy -= 1; pushEv(ev, { t: 'move', x: x, y: y, text: 'You step ' + D.word + '.' }); }
    p.x = x; p.y = y;
    if (p.energy <= 0) { p.energy = 0; endRun(st, ev, 'dead', 'you ran out of Energy'); return true; }
    collectHere(st, ev);
    return true;
  }
  function spendStrike(st, ev) { // attacks cost 0, or 2 under Frostbite
    var p = st.player;
    if (p.frostbite > 0) { p.energy -= 2; pushEv(ev, { t: 'hit', x: p.x, y: p.y, enemyId: null, dmg: 2, text: 'Frostbite: the attack costs 2 Energy.' }); if (p.energy <= 0) { p.energy = 0; endRun(st, ev, 'dead', 'Frostbite'); } }
  }
  function shotRange(st) { return st.player.energy >= 40 ? 5 : st.player.energy >= 15 ? 4 : 3; } // the game uses your vision radius
  function useItem(st, ev, key, dir) {
    var p = st.player, D = DIRS[dir], cfg = ITEMS[key], line, i, e, hits = 0, x, y;
    if (key === 'single_shot' || key === 'piercing_shot') {
      line = lineTiles(st, p.x, p.y, dir, shotRange(st));
      pushEv(ev, { t: 'item', x: p.x, y: p.y, value: 0, text: 'You fire the ' + cfg.name + ' ' + D.word + '.' });
      for (i = 0; i < line.length; i++) {
        e = enemyAt(st, line[i].x, line[i].y);
        if (!e) continue;
        hits += 1;
        damageEnemy(st, ev, e, cfg.dmg, cfg.name);
        if (key === 'single_shot' || e.invincible || e.shield > 0 || hits >= 3) break;
      }
      if (!hits) pushEv(ev, { t: 'item', x: p.x, y: p.y, value: 0, text: 'The arrow hits nothing.' });
      return;
    }
    if (key === 'pogo_stick') {
      x = p.x + 2 * D.dx; y = p.y + 2 * D.dy;
      p.energy -= cfg.cost; p.x = x; p.y = y;
      pushEv(ev, { t: 'item', x: x, y: y, value: 0, text: 'Pogo Stick: you jump ' + D.word + ' over the tile in front of you.' });
      if (p.energy <= 0) { p.energy = 0; endRun(st, ev, 'dead', 'you ran out of Energy'); return; }
      collectHere(st, ev);
      return;
    }
    if (key === 'bomb') {
      x = p.x + D.dx; y = p.y + D.dy;
      st.bombs.push({ id: nextId(st, 'b'), x: x, y: y, turns: cfg.timer });
      pushEv(ev, { t: 'item', x: x, y: y, value: 0, text: 'You place a Bomb ' + D.word + ': it blows up 3x3 in ' + cfg.timer + ' turns and hits you too.' });
    }
  }

  /* ===================================================================================================
   * 10. Traps, bombs and weather tick
   * =================================================================================================== */
  function trapsTick(st, ev) {
    var p = st.player, i, t, line, j, b, s, D, nx, ny, e;
    if (p.poison > 0) { p.poison -= 1; p.energy -= 1; pushEv(ev, { t: 'hit', x: p.x, y: p.y, enemyId: null, dmg: 1, text: 'Poison: 1 Energy.' }); if (p.energy <= 0) { p.energy = 0; endRun(st, ev, 'dead', 'poison'); return; } }
    if (p.frostbite > 0) p.frostbite -= 1;
    for (i = 0; i < st.traps.length; i++) {
      t = st.traps[i];
      if (t.type === 'spike') {
        t.up = st.turn % 2 === 1;
        if (t.up && p.x === t.x && p.y === t.y) { hurt(st, ev, rngInt(st, TRAPS.spike.dmg[0], TRAPS.spike.dmg[1]), 'spikes', null, 'spike', 'Spikes hit you for '); if (st.status !== 'playing') return; }
      } else if (t.type === 'arrow') {
        t.timer -= 1;
        if (t.timer > 0) continue;
        t.timer = TRAPS.arrow.every;
        line = arrowLine(st, t);
        if (inZone(line, p.x, p.y)) { hurt(st, ev, rngInt(st, TRAPS.arrow.dmg[0], TRAPS.arrow.dmg[1]), 'an arrow trap', null, 'arrow', 'An arrow hits you for '); if (st.status !== 'playing') return; }
        else pushEv(ev, { t: 'arrow', x: t.x, y: t.y, dmg: 0, text: 'An arrow flies ' + DIRS[t.dir].word + ' from the trap.' });
      }
    }
    for (i = st.bombs.length - 1; i >= 0; i--) {
      b = st.bombs[i];
      b.turns -= 1;
      if (b.turns > 0) continue;
      st.bombs.splice(i, 1);
      pushEv(ev, { t: 'explode', x: b.x, y: b.y, dmg: ITEMS.bomb.dmg, text: 'The Bomb explodes.' });
      for (j = st.enemies.length - 1; j >= 0; j--) { e = st.enemies[j]; if (cheb(e.x, e.y, b.x, b.y) <= 1) damageEnemy(st, ev, e, ITEMS.bomb.dmg, 'The Bomb'); }
      if (cheb(p.x, p.y, b.x, b.y) <= 1) { hurt(st, ev, ITEMS.bomb.dmg, 'your own Bomb', null, 'explode', 'Your own Bomb hits you for '); if (st.status !== 'playing') return; }
    }
    if (st.weather === 'storm') {
      for (i = st.strikes.length - 1; i >= 0; i--) {
        s = st.strikes[i]; s.turns -= 1;
        if (s.turns > 0) continue;
        st.strikes.splice(i, 1);
        if (p.x === s.x && p.y === s.y) { hurt(st, ev, 25, 'lightning', null, 'hit', 'Lightning hits you for '); if (st.status !== 'playing') return; }
        else pushEv(ev, { t: 'explode', x: s.x, y: s.y, dmg: 0, text: 'Lightning strikes the marked tile.' });
      }
      if (st.turn % 4 === 2) { st.strikes.push({ x: p.x, y: p.y, turns: 1 }); pushEv(ev, { t: 'enemy_charge', x: p.x, y: p.y, enemyId: 'storm', text: 'The storm marks your tile: lightning hits it next turn.' }); }
    }
    if (st.weather === 'gale' && st.turn % 4 === 0 && st.wind) {
      D = DIRS[st.wind]; nx = p.x + D.dx; ny = p.y + D.dy;
      if (!solidAt(st, nx, ny) && !enemyAt(st, nx, ny)) {
        p.x = nx; p.y = ny;
        pushEv(ev, { t: 'move', x: nx, y: ny, text: 'A gust pushes you ' + D.word + '.' });
        collectHere(st, ev);
        if (st.status !== 'playing') return;
      }
      for (i = 0; i < st.enemies.length; i++) {
        e = st.enemies[i];
        if (ENEMIES[e.type].rooted) continue;
        nx = e.x + D.dx; ny = e.y + D.dy;
        if (freeForEnemy(st, nx, ny, e)) { e.x = nx; e.y = ny; pushEv(ev, { t: 'enemy_move', x: nx, y: ny, enemyId: e.id, text: 'The gust pushes the ' + ename(e) + ' ' + D.word + '.' }); }
      }
    }
  }
  function arrowLine(st, t) { // from the tile next to the stone until a wall or a solid object
    var D = DIRS[t.dir], out = [], x = t.x + D.dx, y = t.y + D.dy, o;
    while (!isWall(st, x, y)) { o = objectAt(st, x, y); if (o && SOLID_OBJECTS[o.type]) break; out.push({ x: x, y: y }); x += D.dx; y += D.dy; }
    return out;
  }

  /* ===================================================================================================
   * 11. Enemy phase machine
   * =================================================================================================== */
  function findTarget(st, e, cfg) { // can the enemy start a wind-up right now? -> { target, dir, zone } or null
    var p = st.player, k = cfg.kind, d, line, range;
    if (k === 'passive') return null;
    if (cfg.ambush && !e.revealed) { if (manh(e.x, e.y, p.x, p.y) === 1) e.revealed = true; else return null; }
    if (k === 'melee' || k === 'hop' || k === 'leap' || k === 'aoe') {
      if (manh(e.x, e.y, p.x, p.y) !== 1) return null;
      return { target: { x: p.x, y: p.y }, dir: dirTo(e.x, e.y, p.x, p.y), zone: k === 'aoe' ? n4(st, e.x, e.y) : [{ x: p.x, y: p.y }] };
    }
    if (k === 'dash' || k === 'reach' || k === 'projectile') {
      d = lineDirTo(e.x, e.y, p.x, p.y); if (!d) return null;
      range = cfg.range;
      line = lineTiles(st, e.x, e.y, d, range);
      if (!inZone(line, p.x, p.y)) return null;
      return { target: { x: p.x, y: p.y }, dir: d, zone: line };
    }
    if (k === 'explode' || k === 'spawner' || k === 'thrower') {
      if (cheb(e.x, e.y, p.x, p.y) > cfg.aggro) return null;
      if (k === 'spawner' && e.spawns <= 0) return null;
      if (k === 'thrower' && thrownAlive(st, e) >= 2) return null;
      return { target: { x: p.x, y: p.y }, dir: dirTo(e.x, e.y, p.x, p.y), zone: k === 'explode' ? ring8(st, e.x, e.y, false) : [] };
    }
    return null;
  }
  function thrownAlive(st, lob) { var n = 0, i; for (i = 0; i < st.enemies.length; i++) if (st.enemies[i].thrown === lob.id) n++; return n; }
  function chargeText(st, e, cfg) {
    var n = e.turns, when = n === 1 ? 'next turn' : 'in ' + n + ' turns', name = ename(e), k = cfg.kind, axis = e.dir === 'up' || e.dir === 'down' ? 'column' : 'row';
    if (k === 'dash') return name + ' winds up: it dashes ' + DIRS[e.dir].word + ' along your ' + axis + ' ' + when + '.';
    if (k === 'aoe') return name + ' winds up: it strikes all four tiles around it ' + when + '.';
    if (k === 'reach') return name + ' winds up: it lashes ' + DIRS[e.dir].word + ', reaching ' + cfg.range + ' tiles, ' + when + '.';
    if (k === 'projectile') return name + ' draws its bow: an arrow flies ' + DIRS[e.dir].word + ' along your ' + axis + ' ' + when + '.';
    if (k === 'explode') return name + ' starts its timer: it explodes 3x3 in ' + n + ' turns.';
    if (k === 'hop' || k === 'leap') return name + ' crouches: it lands on your tile ' + when + '.';
    if (k === 'spawner') return name + ' stirs: a Blue frog hatches in ' + n + ' turns.';
    if (k === 'thrower') return name + ' takes aim: it throws an Exploding mushroom in ' + n + ' turns.';
    return name + ' winds up at your tile: it strikes ' + when + '.';
  }
  function startCharge(st, ev, e, cfg, t) {
    var n = cfg.charge;
    if (st.weather === 'heatwave') n = Math.max(1, n + rngInt(st, -1, 1));
    e.phase = 'charge'; e.turns = n; e.target = t.target; e.dir = t.dir; e.zone = t.zone;
    pushEv(ev, { t: 'enemy_charge', x: e.x, y: e.y, enemyId: e.id, text: chargeText(st, e, cfg) });
  }
  function prefOrder(ax, ay, bx, by, away) { // directions from (ax,ay) ordered by how directly they lead toward (bx,by), or away from it
    var dx = bx - ax, dy = by - ay, h = dx >= 0 ? 'right' : 'left', v = dy >= 0 ? 'down' : 'up', first = Math.abs(dx) >= Math.abs(dy) ? h : v, second = first === h ? v : h;
    var order = [first, second, OPPOSITE[second], OPPOSITE[first]];
    return away ? order.reverse() : order;
  }
  function stepToward(st, ev, e, cfg, away) { // one greedy step toward (or away from) the hero; returns true if moved
    var p = st.player, best = null, bestD = away ? -1 : Infinity, i, D, x, y, d, cur = manh(e.x, e.y, p.x, p.y), order = prefOrder(e.x, e.y, p.x, p.y, away);
    for (i = 0; i < 4; i++) {
      D = DIRS[order[i]]; x = e.x + D.dx; y = e.y + D.dy;
      if (!freeForEnemy(st, x, y, e)) continue;
      d = manh(x, y, p.x, p.y);
      if (away ? d > bestD : d < bestD) { bestD = d; best = { x: x, y: y }; }
    }
    if (!best || (away ? bestD <= cur : bestD >= cur)) return false;
    e.x = best.x; e.y = best.y;
    pushEv(ev, { t: 'enemy_move', x: e.x, y: e.y, enemyId: e.id, text: 'The ' + ename(e) + (away ? ' runs away.' : ' moves closer.') });
    return true;
  }
  function wanderStep(st, ev, e) {
    var opts = [], i, D, x, y, pick;
    if (rngNext(st) >= 0.6) return;
    for (i = 0; i < 4; i++) { D = DIRS[DIR_IDS[i]]; x = e.x + D.dx; y = e.y + D.dy; if (freeForEnemy(st, x, y, e)) opts.push({ x: x, y: y }); }
    pick = rngPick(st, opts);
    if (!pick) return;
    e.x = pick.x; e.y = pick.y;
    pushEv(ev, { t: 'enemy_move', x: e.x, y: e.y, enemyId: e.id, text: 'The ' + ename(e) + ' wanders.' });
  }
  function idleMove(st, ev, e, cfg) {
    var p = st.player, near = cheb(e.x, e.y, p.x, p.y) <= cfg.aggro;
    if (cfg.rooted) return;
    if (cfg.ambush && !e.revealed) return;
    if (cfg.invincible) { if (near && e.clock % cfg.every === 0) stepToward(st, ev, e, cfg, false); return; }
    if (cfg.aggro > 0 && near) { if (stepToward(st, ev, e, cfg, false)) return; }
    if (cfg.wander) wanderStep(st, ev, e);
  }
  function spawnEnemy(st, ev, type, x, y, extra) {
    var cfg = ENEMIES[type], n = { id: nextId(st, 'e'), type: type, x: x, y: y, hp: cfg.hp, maxHp: cfg.hp, phase: 'idle', turns: 0, target: null, dir: null, shield: 0, invincible: !!cfg.invincible, zone: [], clock: 0, spawns: 0, flee: 0, revealed: true, thrown: extra && extra.thrown ? extra.thrown : null };
    st.enemies.push(n);
    updateShields(st);
    return n;
  }
  function freeNeighbours(st, x, y, eight) {
    var tiles = eight ? ring8(st, x, y, false) : n4(st, x, y), out = [], i, t;
    for (i = 0; i < tiles.length; i++) { t = tiles[i]; if (!solidAt(st, t.x, t.y) && !enemyAt(st, t.x, t.y) && !(st.player.x === t.x && st.player.y === t.y) && !objectAt(st, t.x, t.y)) out.push(t); }
    return out;
  }
  function fire(st, ev, e, cfg) { // the wind-up ends: resolve the attack
    var p = st.player, k = cfg.kind, hit, dmg, i, last, tile, spot, n, zone = e.zone;
    if (k === 'explode') zone = ring8(st, e.x, e.y, true);
    hit = inZone(zone, p.x, p.y);
    e.phase = 'attack'; e.turns = 0;
    if (k === 'spawner') {
      spot = rngPick(st, freeNeighbours(st, e.x, e.y, false));
      if (spot) { e.spawns -= 1; n = spawnEnemy(st, ev, 'frogglet', spot.x, spot.y, null); pushEv(ev, { t: 'spawn', x: spot.x, y: spot.y, enemyId: n.id, text: 'A Blue frog hatches from the ' + ename(e) + '.' }); }
      e.phase = 'idle'; e.target = null; e.dir = null; e.zone = [];
      if (e.spawns > 0 && cheb(e.x, e.y, p.x, p.y) <= cfg.aggro) { e.phase = 'charge'; e.turns = cfg.charge; }
      return;
    }
    if (k === 'thrower') {
      spot = rngPick(st, freeNeighbours(st, p.x, p.y, true));
      if (spot) { n = spawnEnemy(st, ev, 'boomcap', spot.x, spot.y, { thrown: e.id }); pushEv(ev, { t: 'spawn', x: spot.x, y: spot.y, enemyId: n.id, text: 'The ' + ename(e) + ' throws an Exploding mushroom next to you.' }); }
      e.phase = 'idle'; e.target = null; e.dir = null; e.zone = [];
      return;
    }
    if (k === 'explode') {
      pushEv(ev, { t: 'explode', x: e.x, y: e.y, enemyId: e.id, dmg: 0, text: 'The ' + ename(e) + ' explodes.' });
      removeEnemy(st, e);
      if (hit) hurt(st, ev, rngInt(st, cfg.dmg[0], cfg.dmg[1]), 'the explosion', null, 'explode', 'The explosion hits you for ');
      return;
    }
    if (hit) { dmg = rngInt(st, cfg.dmg[0], cfg.dmg[1]); hurt(st, ev, dmg, aAn(ename(e)), e, 'hit'); }
    else pushEv(ev, { t: 'enemy_attack', x: e.target ? e.target.x : e.x, y: e.target ? e.target.y : e.y, enemyId: e.id, dmg: 0, text: 'The ' + ename(e) + (k === 'dash' ? ' dashes' : k === 'projectile' ? ' fires' : k === 'reach' ? ' lashes' : k === 'hop' || k === 'leap' ? ' lands' : ' strikes') + ' and misses.' });
    if (k === 'dash') { // fly along the line to the last free tile, stopping before anything solid or the hero
      last = null;
      for (i = 0; i < zone.length; i++) { tile = zone[i]; if (solidAt(st, tile.x, tile.y) || enemyAt(st, tile.x, tile.y) || (p.x === tile.x && p.y === tile.y)) break; last = tile; }
      if (last) { e.x = last.x; e.y = last.y; }
    } else if ((k === 'hop' || k === 'leap') && !hit && e.target && freeForEnemy(st, e.target.x, e.target.y, e)) { e.x = e.target.x; e.y = e.target.y; }
    if (k === 'projectile' && st.enemies.indexOf(e) >= 0) { e.phase = 'rest'; e.flee = cfg.flee; e.turns = cfg.flee; pushEv(ev, { t: 'flee', x: e.x, y: e.y, enemyId: e.id, text: 'The ' + ename(e) + ' runs away for ' + cfg.flee + ' turns.' }); }
    e.target = null; e.dir = null; e.zone = [];
  }
  function enemyTick(st, ev, e) {
    var cfg = ENEMIES[e.type], t;
    if (!cfg || st.status !== 'playing') return;
    e.clock += 1;
    if (e.phase === 'charge') {
      if (cfg.kind === 'explode' && e.turns > 1) stepToward(st, ev, e, cfg, false);
      e.turns -= 1;
      if (e.turns > 0) { if (cfg.kind === 'explode') e.zone = ring8(st, e.x, e.y, false); return; }
      fire(st, ev, e, cfg);
      return;
    }
    if (e.phase === 'attack') { if (cfg.rest > 0) { e.phase = 'rest'; e.turns = cfg.rest; } else { e.phase = 'idle'; e.turns = 0; } return; }
    if (e.phase === 'rest') {
      if (e.flee > 0) { e.flee -= 1; e.turns = e.flee; stepToward(st, ev, e, cfg, true); if (e.flee <= 0) { e.phase = 'idle'; e.turns = 0; } return; }
      e.turns -= 1; if (e.turns <= 0) { e.phase = 'idle'; e.turns = 0; }
      return;
    }
    t = findTarget(st, e, cfg);
    if (t) { startCharge(st, ev, e, cfg, t); return; }
    idleMove(st, ev, e, cfg);
  }

  /* ===================================================================================================
   * 12. step(state, id, opts)
   * =================================================================================================== */
  var LOGGED = { attack: 1, kill: 1, smash: 1, drop: 1, pickup: 1, item: 1, enemy_charge: 1, hit: 1, blocked_hit: 1, spike: 1, arrow: 1, explode: 1, spawn: 1, flee: 1, thaw: 1, win: 1, dead: 1, despawn: 1, enemy_attack: 1 };
  function step(state, id, opts) {
    var st = clone(state), ev = [], ids, i, e, pk;
    if (st.status !== 'playing') { pushEv(ev, { t: 'blocked', x: st.player.x, y: st.player.y, text: 'The run is over.' }); return { state: st, events: ev }; }
    st.turn += 1; // the press is turn N; a refused press hands back an untouched copy
    if (!heroPress(st, ev, String(id), opts)) return { state: clone(state), events: ev };
    if (st.status === 'playing') trapsTick(st, ev);
    if (st.status === 'playing') {
      ids = st.enemies.map(function (x) { return x.id; });
      for (i = 0; i < ids.length && st.status === 'playing'; i++) {
        e = null;
        st.enemies.forEach(function (x) { if (x.id === ids[i]) e = x; });
        if (e) enemyTick(st, ev, e);
      }
    }
    if (st.status === 'playing') {
      for (i = st.pickups.length - 1; i >= 0; i--) {
        pk = st.pickups[i];
        if (pk.fresh) { pk.fresh = false; continue; }
        if (pk.despawn > 0) { pk.despawn -= 1; if (pk.despawn === 0) { st.pickups.splice(i, 1); pushEv(ev, { t: 'despawn', x: pk.x, y: pk.y, text: 'The ' + pickupName(pk) + ' fades away.' }); } }
      }
    }
    for (i = 0; i < ev.length; i++) if (LOGGED[ev[i].t] && ev[i].text) st.log.push({ turn: st.turn, text: ev[i].text });
    while (st.log.length > 60) st.log.shift();
    return { state: st, events: ev };
  }

  /* ===================================================================================================
   * 13. cues(state): what the game telegraphs right now
   * =================================================================================================== */
  function cues(st) {
    var out = [], i, j, e, cfg, kind, zone, t, b, line; // under heatwave the zones stay visible, only the timing is unreliable
    for (i = 0; i < st.enemies.length; i++) {
      e = st.enemies[i]; cfg = ENEMIES[e.type];
      if (e.phase !== 'charge' || !cfg) continue;
      kind = cfg.kind;
      if (kind === 'explode') { if (e.turns !== 1) continue; zone = ring8(st, e.x, e.y, false); kind = 'explode'; }
      else if (kind === 'aoe') zone = e.zone;
      else if (kind === 'dash' || kind === 'reach' || kind === 'projectile') { zone = e.zone; kind = 'line'; }
      else if (kind === 'melee' || kind === 'hop' || kind === 'leap') { zone = e.zone; kind = 'target'; }
      else continue;
      for (j = 0; j < zone.length; j++) out.push({ x: zone[j].x, y: zone[j].y, kind: kind, enemyId: e.id });
    }
    for (i = 0; i < st.bombs.length; i++) { b = st.bombs[i]; if (b.turns !== 1) continue; zone = ring8(st, b.x, b.y, true); for (j = 0; j < zone.length; j++) out.push({ x: zone[j].x, y: zone[j].y, kind: 'explode', enemyId: b.id }); }
    for (i = 0; i < st.strikes.length; i++) out.push({ x: st.strikes[i].x, y: st.strikes[i].y, kind: 'target', enemyId: 'storm' });
    for (i = 0; i < st.traps.length; i++) { t = st.traps[i]; if (t.type !== 'arrow' || t.timer !== 1) continue; line = arrowLine(st, t); for (j = 0; j < line.length; j++) out.push({ x: line[j].x, y: line[j].y, kind: 'line', enemyId: t.id }); }
    return out;
  }

  /* ===================================================================================================
   * 14. Samples: hand designed 14x9 floors
   * =================================================================================================== */
  function floor(name, rows, o) {
    return { v: 1, w: rows[0].length, h: rows.length, name: name, weather: o.weather || null, tiles: rows.join('\n'), start: o.start,
      enemies: o.enemies || [], objects: o.objects || [], pickups: o.pickups || [], traps: o.traps || [],
      hero: { energy: HERO.energy, maxEnergy: HERO.maxEnergy, atk: HERO.atk, items: o.items || [], talents: o.talents || [] } };
  }
  var SAMPLE_BUILDERS = {
    'gauntlet': function () {
      return floor('The Gauntlet', [
        '##############',
        '#....#.......#',
        '#.##.#.#####.#',
        '#.#..#.#...#.#',
        '#.#....#.#.#.#',
        '#.##.#.#.#...#',
        '#....#.#.###.#',
        '#....#.......#',
        '##############'
      ], {
        start: { x: 1, y: 4 },
        enemies: [{ type: 'bat', x: 9, y: 1 }, { type: 'mediumslime', x: 3, y: 3 }, { type: 'mediumslime', x: 8, y: 5 }, { type: 'whipweed', x: 3, y: 7 }, { type: 'skelearcher', x: 12, y: 1 }],
        objects: [{ type: 'stairs', x: 12, y: 4 }, { type: 'pot', x: 4, y: 7 }, { type: 'pot', x: 4, y: 6 }, { type: 'pot', x: 9, y: 3 }, { type: 'pot', x: 10, y: 7 }, { type: 'corn_stalk', x: 2, y: 6 }, { type: 'corn_stalk', x: 12, y: 7 }, { type: 'crate', x: 10, y: 1 }],
        pickups: [{ type: 'item', x: 3, y: 4, item: 'single_shot' }, { type: 'small_energy_orb', x: 8, y: 3 }, { type: 'treasure', x: 6, y: 6 }],
        traps: [{ type: 'spike', x: 6, y: 4 }, { type: 'spike', x: 8, y: 7 }, { type: 'arrow', x: 0, y: 7, dir: 'right' }]
      });
    },
    'frog pond': function () {
      return floor('Frog Pond', [
        '##############',
        '#............#',
        '#.##......##.#',
        '#.#........#.#',
        '#............#',
        '#.#........#.#',
        '#.##......##.#',
        '#............#',
        '##############'
      ], {
        weather: 'blizzard',
        start: { x: 1, y: 4 },
        enemies: [{ type: 'frogspawn', x: 7, y: 4 }, { type: 'croaker', x: 10, y: 7 }, { type: 'frogglet', x: 5, y: 6 }, { type: 'frogglet', x: 9, y: 3 }, { type: 'smallslime', x: 4, y: 1 }],
        objects: [{ type: 'stairs', x: 12, y: 7 }, { type: 'pot', x: 4, y: 3 }, { type: 'pot', x: 10, y: 5 }, { type: 'crate', x: 7, y: 7 }, { type: 'corn_stalk', x: 2, y: 7 }, { type: 'corn_stalk', x: 12, y: 1 }, { type: 'fountain', x: 1, y: 1 }],
        pickups: [{ type: 'small_energy_orb', x: 3, y: 1 }, { type: 'small_energy_orb', x: 11, y: 4 }, { type: 'large_energy_orb', x: 7, y: 1 }, { type: 'treasure', x: 12, y: 4 }, { type: 'golden_corn', x: 7, y: 3 }],
        traps: [{ type: 'spike', x: 6, y: 4 }, { type: 'spike', x: 8, y: 4 }],
        items: ['pogo_stick']
      });
    },
    'dragma hall': function () {
      return floor('Dragma Hall', [
        '##############',
        '#............#',
        '#.#.#.##.#.#.#',
        '#............#',
        '#.#.#.##.#.#.#',
        '#............#',
        '#.#.#.##.#.#.#',
        '#............#',
        '##############'
      ], {
        weather: 'heatwave',
        start: { x: 1, y: 4 },
        enemies: [{ type: 'dragma_skelesoldier', x: 5, y: 3 }, { type: 'dragma_skelesoldier', x: 8, y: 5 }, { type: 'dragma_bat', x: 12, y: 1 }, { type: 'ghost3', x: 7, y: 5 }],
        objects: [{ type: 'stairs', x: 12, y: 4 }, { type: 'pot', x: 3, y: 1 }, { type: 'pot', x: 10, y: 7 }, { type: 'crate', x: 3, y: 7 }, { type: 'crate', x: 10, y: 1 }, { type: 'chest', x: 7, y: 1 }, { type: 'corn_stalk', x: 1, y: 7 }, { type: 'corn_stalk', x: 12, y: 7 }],
        pickups: [{ type: 'large_energy_orb', x: 7, y: 7 }, { type: 'treasure', x: 5, y: 7 }, { type: 'golden_corn', x: 1, y: 1 }],
        traps: [{ type: 'spike', x: 3, y: 5 }, { type: 'spike', x: 10, y: 3 }],
        items: ['single_shot'],
        talents: ['armor_plating']
      });
    }
  };
  var SAMPLES = ['gauntlet', 'frog pond', 'dragma hall'];
  function sample(name) { var b = SAMPLE_BUILDERS[String(name || 'gauntlet').toLowerCase()] || SAMPLE_BUILDERS.gauntlet; return b(); }

  /* ===================================================================================================
   * 15. Export
   * =================================================================================================== */
  var MOG_SIM = { RULES: RULES, validate: validate, newGame: newGame, actions: actions, step: step, cues: cues, encode: encode, decode: decode, sample: sample, SAMPLES: SAMPLES, DIRS: DIRS, VERSION: '1.0' };
  if (typeof module !== 'undefined' && module.exports) module.exports = MOG_SIM;
  if (root) root.MOG_SIM = MOG_SIM;
})(typeof window !== 'undefined' ? window : (typeof globalThis !== 'undefined' ? globalThis : null));
