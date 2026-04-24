const http = require("http");
const fs = require("fs");
const path = require("path");
const WebSocket = require("ws");

const PORT = process.env.PORT || 3000;
const MAX_PLAYERS = 9;
const SMALL_BLIND = 10;
const BIG_BLIND = 20;
const STARTING_CHIPS = 2000;
const ROUND_ORDER = ["preflop", "flop", "turn", "river", "showdown"];

const rooms = new Map();
const socketsById = new Map();
let playerSeq = 1;

function createDeck() {
  const suits = ["S", "H", "D", "C"];
  const ranks = ["2", "3", "4", "5", "6", "7", "8", "9", "T", "J", "Q", "K", "A"];
  const deck = [];
  for (const suit of suits) {
    for (const rank of ranks) {
      deck.push(rank + suit);
    }
  }
  for (let i = deck.length - 1; i > 0; i -= 1) {
    const j = Math.floor(Math.random() * (i + 1));
    [deck[i], deck[j]] = [deck[j], deck[i]];
  }
  return deck;
}

function cardValue(rank) {
  return "23456789TJQKA".indexOf(rank) + 2;
}

function combinations(arr, k) {
  const out = [];
  function helper(start, combo) {
    if (combo.length === k) {
      out.push(combo.slice());
      return;
    }
    for (let i = start; i < arr.length; i += 1) {
      combo.push(arr[i]);
      helper(i + 1, combo);
      combo.pop();
    }
  }
  helper(0, []);
  return out;
}

function evaluate5(cards) {
  const ranks = cards.map((c) => c[0]);
  const suits = cards.map((c) => c[1]);
  const values = ranks.map(cardValue).sort((a, b) => b - a);
  const counts = new Map();
  for (const v of values) counts.set(v, (counts.get(v) || 0) + 1);
  const groups = [...counts.entries()].sort((a, b) => {
    if (b[1] !== a[1]) return b[1] - a[1];
    return b[0] - a[0];
  });
  const isFlush = suits.every((s) => s === suits[0]);
  const uniqVals = [...new Set(values)].sort((a, b) => b - a);
  let isStraight = false;
  let straightHigh = 0;
  if (uniqVals.length === 5) {
    if (uniqVals[0] - uniqVals[4] === 4) {
      isStraight = true;
      straightHigh = uniqVals[0];
    } else if (
      uniqVals[0] === 14 &&
      uniqVals[1] === 5 &&
      uniqVals[2] === 4 &&
      uniqVals[3] === 3 &&
      uniqVals[4] === 2
    ) {
      isStraight = true;
      straightHigh = 5;
    }
  }

  if (isStraight && isFlush) return [8, straightHigh];
  if (groups[0][1] === 4) return [7, groups[0][0], groups[1][0]];
  if (groups[0][1] === 3 && groups[1][1] === 2) return [6, groups[0][0], groups[1][0]];
  if (isFlush) return [5, ...values];
  if (isStraight) return [4, straightHigh];
  if (groups[0][1] === 3) {
    const kickers = groups.filter((g) => g[1] === 1).map((g) => g[0]).sort((a, b) => b - a);
    return [3, groups[0][0], ...kickers];
  }
  if (groups[0][1] === 2 && groups[1][1] === 2) {
    const pairHigh = Math.max(groups[0][0], groups[1][0]);
    const pairLow = Math.min(groups[0][0], groups[1][0]);
    const kicker = groups.find((g) => g[1] === 1)[0];
    return [2, pairHigh, pairLow, kicker];
  }
  if (groups[0][1] === 2) {
    const pair = groups[0][0];
    const kickers = groups.filter((g) => g[1] === 1).map((g) => g[0]).sort((a, b) => b - a);
    return [1, pair, ...kickers];
  }
  return [0, ...values];
}

function compareRank(a, b) {
  const len = Math.max(a.length, b.length);
  for (let i = 0; i < len; i += 1) {
    const av = a[i] || 0;
    const bv = b[i] || 0;
    if (av > bv) return 1;
    if (av < bv) return -1;
  }
  return 0;
}

function evaluate7(cards) {
  const all = combinations(cards, 5);
  let best = null;
  for (const c of all) {
    const rank = evaluate5(c);
    if (!best || compareRank(rank, best) > 0) best = rank;
  }
  return best;
}

function createRoom(roomId) {
  return {
    id: roomId,
    players: [],
    inHand: [],
    deck: [],
    pot: 0,
    community: [],
    dealerIndex: -1,
    currentTurn: null,
    currentBet: 0,
    round: "waiting",
    roundBets: {},
    actedThisRound: new Set(),
    handActive: false,
    lastRaiseSize: BIG_BLIND,
    handNumber: 0,
    dealerId: null,
    smallBlindId: null,
    bigBlindId: null
  };
}

function safeSend(ws, payload) {
  if (ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(payload));
}

function broadcast(room, payload) {
  for (const p of room.players) safeSend(p.ws, payload);
}

function publicPlayer(player) {
  return {
    id: player.id,
    name: player.name,
    chips: player.chips,
    seat: player.seat,
    folded: player.folded,
    allIn: player.allIn,
    currentBet: player.currentBet,
    inHand: player.inHand
  };
}

function getStateFor(room, viewerId) {
  let safeTurn = null;
  if (room.handActive && room.currentTurn) {
    const turnPlayer = room.players.find((p) => p.id === room.currentTurn);
    if (turnPlayer && turnPlayer.inHand && !turnPlayer.folded && !turnPlayer.allIn) {
      safeTurn = room.currentTurn;
    }
  }
  return {
    type: "state",
    roomId: room.id,
    round: room.round,
    pot: room.pot,
    currentBet: room.currentBet,
    currentTurn: safeTurn,
    handNumber: room.handNumber,
    dealerId: room.dealerId,
    smallBlindId: room.smallBlindId,
    bigBlindId: room.bigBlindId,
    smallBlind: SMALL_BLIND,
    bigBlind: BIG_BLIND,
    community: room.community,
    players: room.players.map(publicPlayer),
    yourId: viewerId,
    hands: room.players.reduce((acc, p) => {
      if (!room.handActive || !p.inHand || p.cards.length !== 2) {
        acc[p.id] = [];
      } else if (p.id === viewerId || room.round === "showdown") {
        acc[p.id] = p.cards;
      } else {
        acc[p.id] = ["??", "??"];
      }
      return acc;
    }, {})
  };
}

function nextActiveIndex(room, fromIndex) {
  if (!room.inHand.length) return -1;
  let idx = fromIndex;
  for (let i = 0; i < room.inHand.length; i += 1) {
    idx = (idx + 1) % room.inHand.length;
    const p = room.inHand[idx];
    if (!p.folded && !p.allIn && p.inHand) return idx;
  }
  return -1;
}

function playersCanAct(room) {
  return room.inHand.filter((p) => !p.folded && !p.allIn && p.inHand);
}

function resetRoundBets(room) {
  room.currentBet = 0;
  room.lastRaiseSize = BIG_BLIND;
  room.roundBets = {};
  room.actedThisRound.clear();
  for (const p of room.inHand) p.currentBet = 0;
}

function dealCommunity(room, count) {
  for (let i = 0; i < count; i += 1) room.community.push(room.deck.pop());
}

function startRound(room, roundName) {
  room.round = roundName;
  resetRoundBets(room);
  if (roundName === "flop") dealCommunity(room, 3);
  if (roundName === "turn" || roundName === "river") dealCommunity(room, 1);
  const dealerInHandIndex = room.inHand.findIndex((p) => p.id === room.players[room.dealerIndex].id);
  const first = nextActiveIndex(room, dealerInHandIndex);
  room.currentTurn = first >= 0 ? room.inHand[first].id : null;
}

function settleIfSinglePlayer(room) {
  const live = room.inHand.filter((p) => p.inHand && !p.folded);
  if (live.length === 1) {
    live[0].chips += room.pot;
    const winner = live[0];
    room.round = "showdown";
    broadcast(room, {
      type: "handEnded",
      winners: [{ id: winner.id, name: winner.name }],
      amountEach: room.pot,
      reason: "all others folded"
    });
    room.pot = 0;
    room.handActive = false;
    setTimeout(() => {
      maybeStartHand(room);
    }, 2500);
    return true;
  }
  return false;
}

function moveToNextTurnOrRound(room) {
  if (settleIfSinglePlayer(room)) {
    broadcastState(room);
    return;
  }
  const actors = playersCanAct(room);
  if (actors.length <= 1) {
    advanceRound(room);
    return;
  }

  const allMatched = actors.every((p) => p.currentBet === room.currentBet);
  const allActed = actors.every((p) => room.actedThisRound.has(p.id));
  if (allMatched && allActed) {
    advanceRound(room);
    return;
  }

  const turnIndex = room.inHand.findIndex((p) => p.id === room.currentTurn);
  const nextIdx = nextActiveIndex(room, turnIndex);
  room.currentTurn = nextIdx >= 0 ? room.inHand[nextIdx].id : null;
  broadcastState(room);
}

function advanceRound(room) {
  if (settleIfSinglePlayer(room)) {
    broadcastState(room);
    return;
  }
  const idx = ROUND_ORDER.indexOf(room.round);
  if (idx < 0 || idx >= ROUND_ORDER.length - 2) {
    showdown(room);
    return;
  }
  const next = ROUND_ORDER[idx + 1];
  startRound(room, next);
  if (playersCanAct(room).length <= 1) {
    // No more actionable players (all-in/fold); run board to showdown.
    advanceRound(room);
    return;
  }
  broadcastState(room);
}

function showdown(room) {
  room.round = "showdown";
  room.currentTurn = null;
  const contenders = room.inHand.filter((p) => p.inHand && !p.folded);
  const rankById = new Map();
  for (const p of contenders) {
    const rank = evaluate7([...p.cards, ...room.community]);
    p.bestRank = rank;
    rankById.set(p.id, rank);
  }

  const contribLeft = new Map();
  for (const p of room.players) {
    contribLeft.set(p.id, p.totalContribution || 0);
  }

  const payout = new Map();
  let distributed = 0;
  while (true) {
    const positives = [...contribLeft.values()].filter((v) => v > 0);
    if (!positives.length) break;
    const level = Math.min(...positives);
    const participants = room.players.filter((p) => (contribLeft.get(p.id) || 0) > 0);
    const potSize = level * participants.length;
    distributed += potSize;
    for (const p of participants) {
      contribLeft.set(p.id, (contribLeft.get(p.id) || 0) - level);
    }

    const eligible = participants.filter((p) => p.inHand && !p.folded);
    if (!eligible.length) continue;
    let bestRank = null;
    let winners = [];
    for (const p of eligible) {
      const rank = rankById.get(p.id);
      if (!bestRank || compareRank(rank, bestRank) > 0) {
        bestRank = rank;
        winners = [p];
      } else if (compareRank(rank, bestRank) === 0) {
        winners.push(p);
      }
    }
    const split = Math.floor(potSize / winners.length);
    let remainder = potSize % winners.length;
    for (const w of winners) {
      const take = split + (remainder > 0 ? 1 : 0);
      payout.set(w.id, (payout.get(w.id) || 0) + take);
      remainder = Math.max(0, remainder - 1);
    }
  }

  let winnersSummary = [];
  for (const p of contenders) {
    const amount = payout.get(p.id) || 0;
    if (amount > 0) {
      p.chips += amount;
      winnersSummary.push({ id: p.id, name: p.name, rank: p.bestRank, amount });
    }
  }
  winnersSummary = winnersSummary.sort((a, b) => b.amount - a.amount);

  broadcast(room, {
    type: "handEnded",
    winners: winnersSummary,
    amountEach: winnersSummary[0]?.amount || 0
  });
  room.pot = 0;
  room.handActive = false;
  broadcastState(room);
  setTimeout(() => {
    maybeStartHand(room);
  }, 3500);
}

function maybeStartHand(room) {
  const eligible = room.players.filter((p) => p.chips > 0);
  if (room.handActive || eligible.length < 2) {
    if (eligible.length < 2) {
      room.handActive = false;
      room.round = "waiting";
      room.currentTurn = null;
      room.dealerId = null;
      room.smallBlindId = null;
      room.bigBlindId = null;
    }
    broadcastState(room);
    return;
  }

  room.handActive = true;
  room.handNumber += 1;
  room.deck = createDeck();
  room.community = [];
  room.pot = 0;
  room.round = "preflop";
  room.currentBet = 0;
  room.lastRaiseSize = BIG_BLIND;
  room.dealerId = null;
  room.smallBlindId = null;
  room.bigBlindId = null;
  room.roundBets = {};
  room.actedThisRound.clear();

  for (const p of room.players) {
    p.inHand = p.chips > 0;
    p.folded = !p.inHand;
    p.allIn = false;
    p.currentBet = 0;
    p.totalContribution = 0;
    p.cards = p.inHand ? [room.deck.pop(), room.deck.pop()] : [];
  }
  room.inHand = room.players.filter((p) => p.inHand);
  if (room.inHand.length < 2) {
    room.handActive = false;
    room.round = "waiting";
    broadcastState(room);
    return;
  }

  let dealer = room.dealerIndex;
  for (let i = 0; i < room.players.length; i += 1) {
    dealer = (dealer + 1) % room.players.length;
    if (room.players[dealer].chips > 0) break;
  }
  room.dealerIndex = dealer;
  room.dealerId = room.players[dealer].id;

  const dealerPlayerId = room.players[dealer].id;
  const dealerHandIndex = room.inHand.findIndex((p) => p.id === dealerPlayerId);
  let sbIdx;
  let bbIdx;
  if (room.inHand.length === 2) {
    // Heads-up: dealer is small blind, other player is big blind.
    sbIdx = dealerHandIndex;
    bbIdx = nextActiveIndex(room, dealerHandIndex);
  } else {
    sbIdx = nextActiveIndex(room, dealerHandIndex);
    bbIdx = nextActiveIndex(room, sbIdx);
  }

  postBlind(room, room.inHand[sbIdx], SMALL_BLIND);
  postBlind(room, room.inHand[bbIdx], BIG_BLIND);
  room.smallBlindId = room.inHand[sbIdx].id;
  room.bigBlindId = room.inHand[bbIdx].id;
  room.currentBet = BIG_BLIND;
  room.lastRaiseSize = BIG_BLIND;

  room.actedThisRound.clear();
  const firstToAct = nextActiveIndex(room, bbIdx);
  room.currentTurn = firstToAct >= 0 ? room.inHand[firstToAct].id : null;
  broadcastState(room);
}

function postBlind(room, player, amount) {
  const paid = Math.min(player.chips, amount);
  player.chips -= paid;
  player.currentBet += paid;
  player.totalContribution = (player.totalContribution || 0) + paid;
  room.pot += paid;
  if (player.chips === 0) player.allIn = true;
}

function handleAction(room, playerId, action, amount) {
  if (!room.handActive || room.currentTurn !== playerId || room.round === "showdown") return;
  const player = room.players.find((p) => p.id === playerId);
  if (!player || player.folded || player.allIn || !player.inHand) return;

  const toCall = room.currentBet - player.currentBet;
  if (action === "fold") {
    player.folded = true;
    room.actedThisRound.add(player.id);
  } else if (action === "check") {
    if (toCall !== 0) return;
    room.actedThisRound.add(player.id);
  } else if (action === "call") {
    const pay = Math.min(player.chips, toCall);
    player.chips -= pay;
    player.currentBet += pay;
    player.totalContribution = (player.totalContribution || 0) + pay;
    room.pot += pay;
    room.actedThisRound.add(player.id);
    if (player.chips === 0) player.allIn = true;
  } else if (action === "raise") {
    const minRaiseTo = room.currentBet === 0 ? BIG_BLIND : room.currentBet + room.lastRaiseSize;
    const target = Math.max(minRaiseTo, Number(amount) || minRaiseTo);
    const totalNeed = target - player.currentBet;
    if (totalNeed <= toCall) return;
    const pay = Math.min(player.chips, totalNeed);
    if (pay <= 0) return;
    player.chips -= pay;
    player.currentBet += pay;
    player.totalContribution = (player.totalContribution || 0) + pay;
    room.pot += pay;
    if (player.currentBet > room.currentBet) {
      const prevBet = room.currentBet;
      const raiseSize = player.currentBet - prevBet;
      room.currentBet = player.currentBet;
      const isFullRaise = prevBet === 0 ? player.currentBet >= BIG_BLIND : raiseSize >= room.lastRaiseSize;
      if (isFullRaise) {
        room.lastRaiseSize = prevBet === 0 ? player.currentBet : raiseSize;
        room.actedThisRound = new Set([player.id]);
      } else {
        // Short all-in raise: increases current bet, but does not reopen action.
        room.actedThisRound.add(player.id);
      }
    } else {
      room.actedThisRound.add(player.id);
    }
    if (player.chips === 0) player.allIn = true;
  } else {
    return;
  }

  broadcast(room, {
    type: "action",
    playerId: player.id,
    action,
    amount: player.currentBet
  });
  moveToNextTurnOrRound(room);
}

function broadcastState(room) {
  for (const p of room.players) {
    safeSend(p.ws, getStateFor(room, p.id));
  }
}

function onJoin(ws, msg) {
  if (ws.playerId) {
    safeSend(ws, { type: "error", message: "You already joined a room in this window." });
    return;
  }
  const roomId = String(msg.roomId || "default");
  const name = String(msg.name || `Player${playerSeq}`);
  const seat = Number.isInteger(msg.seat) ? msg.seat : null;

  if (!rooms.has(roomId)) rooms.set(roomId, createRoom(roomId));
  const room = rooms.get(roomId);
  if (room.players.length >= MAX_PLAYERS) {
    safeSend(ws, { type: "error", message: "Room is full (max 9 players)." });
    return;
  }

  const usedSeats = new Set(room.players.map((p) => p.seat));
  let finalSeat = seat;
  if (finalSeat == null || usedSeats.has(finalSeat)) {
    for (let s = 0; s < MAX_PLAYERS; s += 1) {
      if (!usedSeats.has(s)) {
        finalSeat = s;
        break;
      }
    }
  }

  const id = `p${playerSeq++}`;
  const player = {
    id,
    name,
    ws,
    seat: finalSeat,
    chips: STARTING_CHIPS,
    cards: [],
    inHand: false,
    folded: false,
    allIn: false,
    currentBet: 0,
    roomId
  };
  socketsById.set(id, ws);
  ws.playerId = id;
  ws.roomId = roomId;

  room.players.push(player);
  room.players.sort((a, b) => a.seat - b.seat);
  safeSend(ws, { type: "joined", playerId: id, roomId, seat: finalSeat });
  broadcast(room, {
    type: "system",
    message: `${name} joined room ${roomId}.`
  });

  maybeStartHand(room);
}

function onLeave(ws) {
  if (!ws.playerId || !ws.roomId) {
    safeSend(ws, { type: "left" });
    return;
  }
  removePlayer(ws);
  ws.playerId = null;
  ws.roomId = null;
  safeSend(ws, { type: "left" });
}

function removePlayer(ws) {
  const { playerId, roomId } = ws;
  if (!playerId || !roomId || !rooms.has(roomId)) return;
  const room = rooms.get(roomId);
  const idx = room.players.findIndex((p) => p.id === playerId);
  if (idx < 0) return;
  const [removed] = room.players.splice(idx, 1);
  if (room.players.length > 0 && room.dealerIndex >= 0) {
    if (idx < room.dealerIndex) room.dealerIndex -= 1;
    if (room.dealerIndex >= room.players.length) room.dealerIndex = 0;
  } else if (room.players.length === 0) {
    room.dealerIndex = -1;
  }
  socketsById.delete(playerId);
  broadcast(room, { type: "system", message: `${removed.name} left the room.` });

  room.inHand = room.players.filter((p) => p.inHand && p.cards.length === 2);
  if (room.currentTurn === playerId) room.currentTurn = null;
  if (room.handActive) {
    moveToNextTurnOrRound(room);
  } else {
    broadcastState(room);
  }

  if (room.players.length === 0) rooms.delete(roomId);
}

const server = http.createServer((req, res) => {
  const target = req.url === "/" ? "index.html" : req.url.replace(/^\/+/, "");
  const filePath = path.join(process.cwd(), target);
  fs.readFile(filePath, (err, data) => {
    if (err) {
      res.writeHead(404);
      res.end("Not Found");
      return;
    }
    const ext = path.extname(filePath).toLowerCase();
    const map = {
      ".html": "text/html",
      ".js": "application/javascript",
      ".css": "text/css"
    };
    res.writeHead(200, { "Content-Type": map[ext] || "text/plain" });
    res.end(data);
  });
});

const wss = new WebSocket.Server({ server });
wss.on("connection", (ws) => {
  safeSend(ws, { type: "hello", message: "Connected. Send join first." });
  ws.on("message", (raw) => {
    let msg;
    try {
      msg = JSON.parse(raw.toString());
    } catch (e) {
      safeSend(ws, { type: "error", message: "Invalid JSON." });
      return;
    }
    if (msg.type === "join") {
      onJoin(ws, msg);
      return;
    }
    if (msg.type === "leave") {
      onLeave(ws);
      return;
    }
    if (!ws.roomId || !rooms.has(ws.roomId)) return;
    const room = rooms.get(ws.roomId);
    if (msg.type === "action") {
      handleAction(room, ws.playerId, msg.action, msg.amount);
    }
    if (msg.type === "start") {
      maybeStartHand(room);
    }
  });

  ws.on("close", () => {
    removePlayer(ws);
  });
});

server.listen(PORT, () => {
  console.log(`Poker server running on http://localhost:${PORT}`);
});
