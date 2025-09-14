const TILE = 64;
const COLS = 12, ROWS = 12;
const SPEED_MS = 200;
const PEGADO_OFFSET = 20;

const NECK_BORDER = '#5c3a20';
const NECK_FILL = '#fea034';

const LEVELS = [
  { level: 1, food: 5, walls: 0 },
  { level: 2, food: 7, walls: 2 },
  { level: 3, food: 9, walls: 4 },
  { level: 4, food: 11, walls: 6 },
  { level: 5, food: 13, walls: 8 },
  { level: 6, food: 15, walls: 10 },
  { level: 7, food: 17, walls: 12 },
  { level: 8, food: 19, walls: 14 },
  { level: 9, food: 21, walls: 16 },
  { level: 10, food: 23, walls: 18 }
];

const canvas = document.getElementById('game');
const ctx = canvas.getContext('2d');

function loadImage(src) {
  return new Promise((resolve) => {
    const img = new Image();
    img.onload = () => resolve(img);
    img.onerror = () => resolve(null);
    img.src = src;
  });
}
const ASSETS = {
  head: 'assets/hamster/Head.png',
  body: 'assets/hamster/Body.png',
  tuna: 'assets/items/Tuna.png',
  heart: 'assets/items/Heart.png',
};
let IMG = { head: null, body: null, tuna: null, heart: null };

const eq = (a, b) => a.col === b.col && a.row === b.row;
const inside = (c, r) => c >= 0 && c < COLS && r >= 0 && r < ROWS;

function randomFreeCell(occupiedSet) {
  for (let tries = 0; tries < 500; tries++) {
    const col = Math.floor(Math.random() * COLS);
    const row = Math.floor(Math.random() * ROWS);
    const key = col + ',' + row;
    if (!occupiedSet.has(key)) return { col, row };
  }
  return null;
}

function dirKeyFromDelta(dx, dy) {
  if (dx === 1 && dy === 0) return 'right';
  if (dx === -1 && dy === 0) return 'left';
  if (dx === 0 && dy === -1) return 'up';
  if (dx === 0 && dy === 1) return 'down';
  return 'right';
}

const DIRS = {
  ArrowUp: { x: 0, y: -1, key: 'up' },
  ArrowDown: { x: 0, y: 1, key: 'down' },
  ArrowLeft: { x: -1, y: 0, key: 'left' },
  ArrowRight: { x: 1, y: 0, key: 'right' },
  w: { x: 0, y: -1, key: 'up' },
  W: { x: 0, y: -1, key: 'up' },
  s: { x: 0, y: 1, key: 'down' },
  S: { x: 0, y: 1, key: 'down' },
  a: { x: -1, y: 0, key: 'left' },
  A: { x: -1, y: 0, key: 'left' },
  d: { x: 1, y: 0, key: 'right' },
  D: { x: 1, y: 0, key: 'right' },
};

let currentLevel = 1;
let lives = 3;
let segments = [];
let dir = DIRS.ArrowRight;
let nextDir = dir;
let growth = 0;
let food = null;
let eaten = 0;
let walls = [];
let paused = false;
let running = false;
let lastTick = 0;
let showingLevelText = false;
let levelTextStartTime = 0;
let showingCountdown = false;
let countdownStartTime = 0;
let countdownValue = 3;
let gameEnded = false;
let levelCompleteAfterAnimation = false;
let showingLevelComplete = false;
let levelTextReason = 'start';
let isAnimating = false;
let animationStartTime = 0;
let frozenPositions = [];
let targetPositions = [];
let lockedOffsets = { head: { x: 0, y: 0 }, body: { x: 0, y: 0 } };

function getNeighbors(col, row) {
  return [
    { col: col + 1, row: row },
    { col: col - 1, row: row },
    { col: col, row: row + 1 },
    { col: col, row: row - 1 }
  ].filter(pos => inside(pos.col, pos.row));
}

function isBlocked(col, row, occupiedSet) {
  return occupiedSet.has(col + ',' + row);
}

function isReachable(startCol, startRow, targetCol, targetRow, occupiedSet) {
  if (startCol === targetCol && startRow === targetRow) return true;
  if (isBlocked(targetCol, targetRow, occupiedSet)) return false;

  const visited = new Set();
  const queue = [{ col: startCol, row: startRow }];
  visited.add(startCol + ',' + startRow);

  while (queue.length > 0) {
    const current = queue.shift();

    for (const neighbor of getNeighbors(current.col, current.row)) {
      const key = neighbor.col + ',' + neighbor.row;

      if (visited.has(key)) continue;
      if (isBlocked(neighbor.col, neighbor.row, occupiedSet)) continue;

      if (neighbor.col === targetCol && neighbor.row === targetRow) {
        return true;
      }

      visited.add(key);
      queue.push(neighbor);
    }
  }

  return false;
}

function countReachableFreeCells(startCol, startRow, occupiedSet) {
  const visited = new Set();
  const queue = [{ col: startCol, row: startRow }];
  visited.add(startCol + ',' + startRow);
  let count = 0;

  while (queue.length > 0) {
    const current = queue.shift();
    count++;

    for (const neighbor of getNeighbors(current.col, current.row)) {
      const key = neighbor.col + ',' + neighbor.row;

      if (visited.has(key)) continue;
      if (isBlocked(neighbor.col, neighbor.row, occupiedSet)) continue;

      visited.add(key);
      queue.push(neighbor);
    }
  }

  return count;
}

function isSafeFoodPosition(foodCol, foodRow) {
  const head = segments[0];
  const occupied = occupiedSet();

  if (!isReachable(head.col, head.row, foodCol, foodRow, occupied)) {
    return false;
  }

  const postEatOccupied = new Set(occupied);
  postEatOccupied.add(foodCol + ',' + foodRow);

  if (growth === 0 && segments.length > 1) {
    const tail = segments[segments.length - 1];
    postEatOccupied.delete(tail.col + ',' + tail.row);
  }

  const freeNeighbors = getNeighbors(foodCol, foodRow)
    .filter(pos => !isBlocked(pos.col, pos.row, postEatOccupied));

  if (freeNeighbors.length < 2) {
    return false;
  }

  const reachableAfterEat = countReachableFreeCells(foodCol, foodRow, postEatOccupied);
  const minRequiredSpace = Math.max(6, segments.length + 2);

  if (reachableAfterEat < minRequiredSpace) {
    return false;
  }

  for (const neighbor of freeNeighbors) {
    const neighborOccupied = new Set(postEatOccupied);
    neighborOccupied.add(foodCol + ',' + foodRow);

    const reachableFromNeighbor = countReachableFreeCells(neighbor.col, neighbor.row, neighborOccupied);
    if (reachableFromNeighbor < Math.max(4, segments.length)) {
      return false;
    }
  }

  const wallNeighbors = getNeighbors(foodCol, foodRow)
    .filter(pos => !inside(pos.col, pos.row) || isBlocked(pos.col, pos.row, occupied));

  if (wallNeighbors.length > 2) {
    return false;
  }

  if (freeNeighbors.length === 2) {
    const neighbor1 = freeNeighbors[0];
    const neighbor2 = freeNeighbors[1];

    const areOpposite = (neighbor1.col === neighbor2.col) || (neighbor1.row === neighbor2.row);

    if (!areOpposite) {
      const space1 = countReachableFreeCells(neighbor1.col, neighbor1.row, postEatOccupied);
      const space2 = countReachableFreeCells(neighbor2.col, neighbor2.row, postEatOccupied);

      if (space1 < segments.length + 3 || space2 < segments.length + 3) {
        return false;
      }
    }
  }

  return true;
}
function initGame() {
  currentLevel = 1;
  lives = 3;
  gameEnded = false;
  showingLevelText = false;
  showingCountdown = false;
  showingLevelComplete = false;
  levelTextReason = 'start';

  initLevel();
}

function initLevel() {
  const levelConfig = LEVELS[currentLevel - 1];
  const c = Math.floor(COLS / 2), r = Math.floor(ROWS / 2);

  segments = [{ col: c, row: r }];

  dir = DIRS.ArrowRight;
  nextDir = dir;
  growth = 0;
  eaten = 0;
  paused = false;
  running = true;

  showingLevelComplete = false;
  levelCompleteAfterAnimation = false;

  isAnimating = false;
  frozenPositions = [];
  targetPositions = [];
  lockedOffsets = { head: { x: 0, y: 0 }, body: { x: 0, y: 0 } };

  generateWalls(levelConfig.walls);
  placeFood();
  updateVisualHUD();

  if (!levelTextReason) {
    levelTextReason = 'start';
  }

  if (levelTextReason === 'start') {
    showLevelText();
  }

  lastTick = performance.now();

  if (!gameEnded) {
    requestAnimationFrame(loop);
  }
}

function generateWalls(wallCount) {
  walls = [];
  const occupied = new Set();

  const c = Math.floor(COLS / 2), r = Math.floor(ROWS / 2);
  occupied.add(c + ',' + r);

  for (let dx = -1; dx <= 1; dx++) {
    for (let dy = -1; dy <= 1; dy++) {
      const nc = c + dx, nr = r + dy;
      if (inside(nc, nr)) {
        occupied.add(nc + ',' + nr);
      }
    }
  }

  for (let i = 0; i < wallCount; i++) {
    const wall = randomFreeCell(occupied);
    if (wall) {
      walls.push(wall);
      occupied.add(wall.col + ',' + wall.row);
    }
  }
}

function occupiedSet() {
  const s = new Set();
  for (const seg of segments) s.add(seg.col + ',' + seg.row);
  for (const wall of walls) s.add(wall.col + ',' + wall.row);
  return s;
}

function placeFood() {
  const occ = occupiedSet();

  const freeCells = [];
  for (let col = 0; col < COLS; col++) {
    for (let row = 0; row < ROWS; row++) {
      if (!occ.has(col + ',' + row)) {
        freeCells.push({ col, row });
      }
    }
  }

  if (freeCells.length === 0) {
    levelComplete();
    return;
  }

  const safeCells = freeCells.filter(cell => isSafeFoodPosition(cell.col, cell.row));

  if (safeCells.length > 0) {
    safeCells.sort((a, b) => {
      const spaceA = countReachableFreeCells(a.col, a.row, occ);
      const spaceB = countReachableFreeCells(b.col, b.row, occ);
      return spaceB - spaceA;
    });

    const safeOptions = safeCells.slice(0, Math.max(3, Math.ceil(safeCells.length * 0.5)));
    const randomIndex = Math.floor(Math.random() * safeOptions.length);
    food = safeOptions[randomIndex];
  } else {
    const head = segments[0];
    const reachableCells = freeCells.filter(cell =>
      isReachable(head.col, head.row, cell.col, cell.row, occ)
    );

    if (reachableCells.length > 0) {
      reachableCells.sort((a, b) => {
        const neighborsA = getNeighbors(a.col, a.row).filter(pos => !isBlocked(pos.col, pos.row, occ)).length;
        const neighborsB = getNeighbors(b.col, b.row).filter(pos => !isBlocked(pos.col, pos.row, occ)).length;
        return neighborsB - neighborsA;
      });

      const betterOptions = reachableCells.slice(0, Math.max(2, Math.ceil(reachableCells.length * 0.3)));
      const randomIndex = Math.floor(Math.random() * betterOptions.length);
      food = betterOptions[randomIndex];
    } else {
      const randomIndex = Math.floor(Math.random() * freeCells.length);
      food = freeCells[randomIndex];
    }
  }
}
function showLevelText() {
  showingLevelText = true;
  levelTextStartTime = performance.now();
}

function startCountdown() {
  showingCountdown = true;
  countdownStartTime = performance.now();
  countdownValue = 3;
}

function loop(now) {

  if (gameEnded && !showingLevelText) {
    draw(now);
    requestAnimationFrame(loop);
    return;
  }

  if (showingLevelText && now - levelTextStartTime >= 2000) {
    if (levelTextReason === 'congratulations') {
      draw(now);
      requestAnimationFrame(loop);
      return;
    }

    showingLevelText = false;

    switch (levelTextReason) {
      case 'gameOver':
        gameEnded = false;
        initGame();
        break;

      case 'death':
        gameEnded = false;
        levelTextReason = 'start';
        initLevel();
        break;

      case 'complete':
        if (currentLevel >= LEVELS.length) {
          gameEnded = true;
          levelTextReason = 'congratulations';
          showingLevelText = true;
          levelTextStartTime = performance.now();
        } else {
          currentLevel++;
          lives = 3;
          levelTextReason = 'start';
          initLevel();
        }
        break;

      case 'start':
      default:
        startCountdown();
        break;
    }
  }

  if (running) {
    if (showingCountdown) {
      const elapsed = now - countdownStartTime;
      if (elapsed >= 1000) {
        countdownValue--;
        if (countdownValue <= 0) {
          showingCountdown = false;
        } else {
          countdownStartTime = now;
        }
      }
    }

    if (!paused && !showingLevelText && !showingCountdown) {
      if (isAnimating) {
        updateAnimation(now);
      } else if (now - lastTick >= SPEED_MS) {
        startNextMove();
        lastTick = now;
      }
    }
  }

  draw(now);
  requestAnimationFrame(loop);
}

function drawCountdown() {
  ctx.fillStyle = 'rgba(0,0,0,.8)';
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  if (countdownValue > 0) {
    ctx.fillStyle = '#7be065';
    ctx.font = 'bold 80px Arcana, system-ui, sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText(countdownValue.toString(), canvas.width / 2, canvas.height / 2 + 20);
  }

  ctx.textAlign = 'left';
}

function startNextMove() {
  if (!isReverse(nextDir)) dir = nextDir;
  const head = segments[0];
  const newHead = { col: head.col + dir.x, row: head.row + dir.y };

  if (!inside(newHead.col, newHead.row)) return gameOver();
  for (let i = 0; i < segments.length; i++) if (eq(newHead, segments[i])) return gameOver();
  for (const wall of walls) if (eq(newHead, wall)) return gameOver();

  const willEat = food && eq(newHead, food);
  if (willEat) {
    eaten++;
    growth++;
    food = null;
    updateVisualHUD();

    const levelConfig = LEVELS[currentLevel - 1];
    if (eaten >= levelConfig.food) {
    } else {
      placeFood();
    }
  }

  frozenPositions = segments.map(seg => ({ ...seg }));

  targetPositions = [newHead, ...segments];
  if (growth === 0) targetPositions.pop();

  calculateLockedOffsets();

  isAnimating = true;
  animationStartTime = performance.now();

  if (willEat) {
    const levelConfig = LEVELS[currentLevel - 1];
    if (eaten >= levelConfig.food) {
      levelCompleteAfterAnimation = true;
    }
  }
}

function calculateLockedOffsets() {
  lockedOffsets = { head: { x: 0, y: 0 }, body: { x: 0, y: 0 } };

  if (eaten === 0) {
    return;
  }

  if (segments.length >= 3) {
    const headCell = frozenPositions[0];
    const firstNeckCell = frozenPositions[1];
    const bodyCell = frozenPositions[frozenPositions.length - 1];
    const lastNeckCell = frozenPositions[frozenPositions.length - 2];

    lockedOffsets.head = offsetTowardNeighbor(headCell, firstNeckCell);
    lockedOffsets.body = offsetTowardNeighbor(bodyCell, lastNeckCell);
  }
}

function offsetTowardNeighbor(fromCell, toCell) {
  if (!fromCell || !toCell) return { x: 0, y: 0 };

  const dx = toCell.col - fromCell.col;
  const dy = toCell.row - fromCell.row;

  const offsetX = Math.sign(dx) * Math.min(PEGADO_OFFSET, Math.abs(dx * TILE));
  const offsetY = Math.sign(dy) * Math.min(PEGADO_OFFSET, Math.abs(dy * TILE));

  return { x: offsetX, y: offsetY };
}

function updateAnimation(now) {
  const elapsed = now - animationStartTime;

  if (elapsed >= SPEED_MS) {
    finishAnimation();
  }
}

function finishAnimation() {
  segments = targetPositions.map(pos => ({ ...pos }));
  if (growth > 0) growth--;

  isAnimating = false;
  frozenPositions = [];
  targetPositions = [];

  if (levelCompleteAfterAnimation) {
    levelCompleteAfterAnimation = false;
    levelComplete();
  }
}

function isReverse(next) {
  if (segments.length < 2) return false;
  const head = segments[0], neck = segments[1];
  const candidate = { col: head.col + next.x, row: head.row + next.y };
  return eq(candidate, neck);
}

function getInterpolatedPosition(index, now) {
  if (!isAnimating) return segments[index];

  const elapsed = now - animationStartTime;
  const t = Math.min(elapsed / SPEED_MS, 1);

  const start = frozenPositions[index] || segments[index];
  const end = targetPositions[index] || start;

  return {
    col: start.col + (end.col - start.col) * t,
    row: start.row + (end.row - start.row) * t,
  };
}

function drawTubeBetween(a, b) {
  const TH = 20;
  const BW = 2;
  const CAP_OVERLAP = 2;

  const ax = a.col * TILE + TILE / 2;
  const ay = a.row * TILE + TILE / 2;
  const bx = b.col * TILE + TILE / 2;
  const by = b.row * TILE + TILE / 2;

  const halfThick = TH / 2;

  if (Math.abs(ax - bx) < 1) {
    const left = Math.round(ax - halfThick);
    const top = Math.round(Math.min(ay, by) - CAP_OVERLAP);
    const h = Math.round(Math.abs(by - ay) + CAP_OVERLAP * 2);

    ctx.fillStyle = NECK_FILL;
    ctx.fillRect(left, top, TH, h);

    ctx.fillStyle = NECK_BORDER;
    ctx.fillRect(left, top, BW, h);
    ctx.fillRect(left + TH - BW, top, BW, h);

  } else if (Math.abs(ay - by) < 1) {
    const top = Math.round(ay - halfThick);
    const left = Math.round(Math.min(ax, bx) - CAP_OVERLAP);
    const w = Math.round(Math.abs(bx - ax) + CAP_OVERLAP * 2);

    ctx.fillStyle = NECK_FILL;
    ctx.fillRect(left, top, w, TH);

    ctx.fillStyle = NECK_BORDER;
    ctx.fillRect(left, top, w, BW);
    ctx.fillRect(left, top + TH - BW, w, BW);
  }
}

function isCornerPosition(index, segmentArray) {
  if (index <= 0 || index >= segmentArray.length - 1) return false;

  const prev = segmentArray[index - 1];
  const curr = segmentArray[index];
  const next = segmentArray[index + 1];

  if (!prev || !curr || !next) return false;

  const v1 = { x: prev.col - curr.col, y: prev.row - curr.row };
  const v2 = { x: next.col - curr.col, y: next.row - curr.row };

  return !((v1.x === 0 && v2.x === 0) || (v1.y === 0 && v2.y === 0));
}

function drawLCornerAt(centerPos, prevPos, nextPos) {
  const TH = 20;
  const BW = 2;
  const CAP_OVERLAP = 2;
  const cx = Math.round(centerPos.col * TILE + TILE / 2);
  const cy = Math.round(centerPos.row * TILE + TILE / 2);
  const halfTile = TILE / 2;
  const halfThick = TH / 2;

  const toPrev = { x: prevPos.col - centerPos.col, y: prevPos.row - centerPos.row };
  const toNext = { x: nextPos.col - centerPos.col, y: nextPos.row - centerPos.row };

  const horizDir = toPrev.x !== 0 ? toPrev.x : (toNext.x !== 0 ? toNext.x : 0);
  const vertDir = toPrev.y !== 0 ? toPrev.y : (toNext.y !== 0 ? toNext.y : 0);

  ctx.fillStyle = NECK_FILL;

  if (horizDir !== 0) {
    const startX = cx;
    const endX = cx + horizDir * halfTile;
    const left = Math.round(Math.min(startX, endX) - CAP_OVERLAP);
    const width = Math.round(Math.abs(endX - startX) + CAP_OVERLAP);

    ctx.fillStyle = NECK_FILL;
    ctx.fillRect(left, Math.round(cy - halfThick), width, TH);

    ctx.fillStyle = NECK_BORDER;
    ctx.fillRect(left, Math.round(cy - halfThick), width, BW);
    ctx.fillRect(left, Math.round(cy + halfThick - BW), width, BW);
  }


  if (vertDir !== 0) {
    const startY = cy;
    const endY = cy + vertDir * halfTile;
    const top = Math.round(Math.min(startY, endY) - CAP_OVERLAP);
    const height = Math.round(Math.abs(endY - startY) + CAP_OVERLAP);

    ctx.fillStyle = NECK_FILL;
    ctx.fillRect(Math.round(cx - halfThick), top, TH, height);

    ctx.fillStyle = NECK_BORDER;
    ctx.fillRect(Math.round(cx - halfThick), top, BW, height);
    ctx.fillRect(Math.round(cx + halfThick - BW), top, BW, height);
  }

  ctx.fillStyle = NECK_FILL;
  ctx.fillRect(Math.round(cx - halfThick), Math.round(cy - halfThick), TH, TH);

  ctx.fillStyle = NECK_BORDER;

  if (horizDir === 0) {
    ctx.fillRect(Math.round(cx - halfThick), Math.round(cy - halfThick), BW, TH);
    ctx.fillRect(Math.round(cx + halfThick - BW), Math.round(cy - halfThick), BW, TH);
  } else if (horizDir > 0) {
    ctx.fillRect(Math.round(cx - halfThick), Math.round(cy - halfThick), BW, TH);
  } else {
    ctx.fillRect(Math.round(cx + halfThick - BW), Math.round(cy - halfThick), BW, TH);
  }

  if (vertDir === 0) {
    ctx.fillRect(Math.round(cx - halfThick), Math.round(cy - halfThick), TH, BW);
    ctx.fillRect(Math.round(cx - halfThick), Math.round(cy + halfThick - BW), TH, BW);
  } else if (vertDir > 0) {
    ctx.fillRect(Math.round(cx - halfThick), Math.round(cy - halfThick), TH, BW);
  } else {
    ctx.fillRect(Math.round(cx - halfThick), Math.round(cy + halfThick - BW), TH, BW);
  }

  if (horizDir > 0 && vertDir > 0) {
    ctx.fillRect(Math.round(cx + halfThick - BW), Math.round(cy + halfThick - BW), BW, BW);
  } else if (horizDir > 0 && vertDir < 0) {
    ctx.fillRect(Math.round(cx + halfThick - BW), Math.round(cy - halfThick), BW, BW);
  } else if (horizDir < 0 && vertDir > 0) {
    ctx.fillRect(Math.round(cx - halfThick), Math.round(cy + halfThick - BW), BW, BW);
  } else if (horizDir < 0 && vertDir < 0) {
    ctx.fillRect(Math.round(cx - halfThick), Math.round(cy - halfThick), BW, BW);
  }
}

function draw(now) {

  ctx.imageSmoothingEnabled = false;


  ctx.fillStyle = '#101116';
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  ctx.strokeStyle = '#1b1c24';
  ctx.lineWidth = 1;
  for (let x = 0; x <= COLS; x++) {
    ctx.beginPath();
    ctx.moveTo(x * TILE + .5, 0);
    ctx.lineTo(x * TILE + .5, canvas.height);
    ctx.stroke();
  }
  for (let y = 0; y <= ROWS; y++) {
    ctx.beginPath();
    ctx.moveTo(0, y * TILE + .5);
    ctx.lineTo(canvas.width, y * TILE + .5);
    ctx.stroke();
  }

  ctx.fillStyle = '#8B4513';
  for (const wall of walls) {
    ctx.fillRect(wall.col * TILE, wall.row * TILE, TILE, TILE);
  }

  if (food) drawSprite(IMG.tuna, food.col, food.row);

  const currentPositions = segments.map((_, i) => getInterpolatedPosition(i, now));

  if (eaten === 0) {
    const pos = currentPositions[0];
    drawSnakeBody(pos, dir.key, { x: 0, y: 0 });
    drawSnakeHead(pos, dir.key, { x: 0, y: 0 });
  } else {
    for (let i = 0; i < currentPositions.length - 1; i++) {
      const aInterpolated = currentPositions[i];
      const bInterpolated = currentPositions[i + 1];
      const aIsCorner = i > 0 && i < segments.length - 1 && isCornerPosition(i, segments);
      const bIsCorner = (i + 1) > 0 && (i + 1) < segments.length - 1 && isCornerPosition(i + 1, segments);
      const aFinal = aIsCorner ? segments[i] : aInterpolated;
      const bFinal = bIsCorner ? segments[i + 1] : bInterpolated;
      drawTubeBetween(aFinal, bFinal);
    }

    for (let i = 1; i < segments.length - 1; i++) {
      const prev = segments[i - 1];
      const curr = segments[i];
      const next = segments[i + 1];
      if (isCornerPosition(i, segments)) {
        drawLCornerAt(curr, prev, next);
      }
    }

    const tailIndex = currentPositions.length - 1;
    const tailPos = currentPositions[tailIndex];
    const tailDir = getSegmentDirection(tailIndex);
    drawSnakeBody(tailPos, tailDir, { x: 0, y: 0 });
    const headPos = currentPositions[0];
    drawSnakeHead(headPos, dir.key, { x: 0, y: 0 });
  }

  drawHUD();
  if (showingCountdown) {
    drawCountdown();
  } else if (showingLevelText) {
    drawLevelText();
  }
}

function drawSprite(img, col, row, offset = { x: 0, y: 0 }) {
  if (!img) return;
  const x = Math.round(col * TILE + offset.x);
  const y = Math.round(row * TILE + offset.y);
  ctx.drawImage(img, x, y, TILE, TILE);
}

function drawSnakeHead(pos, direction, offset = { x: 0, y: 0 }) {
  if (!IMG.head) return;
  const x = Math.round(pos.col * TILE + offset.x);
  const y = Math.round(pos.row * TILE + offset.y);
  const cx = x + TILE / 2, cy = y + TILE / 2;
  ctx.save();
  ctx.translate(cx, cy);
  if (direction === 'right') ctx.rotate(Math.PI / 2);
  else if (direction === 'down') ctx.rotate(Math.PI);
  else if (direction === 'left') ctx.rotate(-Math.PI / 2);
  ctx.drawImage(IMG.head, -TILE / 2, -TILE / 2, TILE, TILE);
  ctx.restore();
}

function drawSnakeBody(pos, direction, offset = { x: 0, y: 0 }) {
  if (!IMG.body) return;
  const x = Math.round(pos.col * TILE + offset.x);
  const y = Math.round(pos.row * TILE + offset.y);
  const cx = x + TILE / 2, cy = y + TILE / 2;
  ctx.save();
  ctx.translate(cx, cy);
  if (direction === 'right') ctx.rotate(Math.PI / 2);
  else if (direction === 'down') ctx.rotate(Math.PI);
  else if (direction === 'left') ctx.rotate(-Math.PI / 2);
  ctx.drawImage(IMG.body, -TILE / 2, -TILE / 2, TILE, TILE);
  ctx.restore();
}

function getSegmentDirection(index) {
  if (index === 0) return dir.key;
  if (index < segments.length - 1) {
    const curr = segments[index];
    const prev = segments[index - 1];
    const dx = prev.col - curr.col;
    const dy = prev.row - curr.row;
    return dirKeyFromDelta(dx, dy);
  }

  const curr = segments[index];
  const prev = segments[index - 1];
  const dx = prev.col - curr.col;
  const dy = prev.row - curr.row;
  return dirKeyFromDelta(dx, dy);
}

function drawHUD() {
  if (paused) {
    ctx.fillStyle = '#ff6868';
    ctx.font = 'bold 24px Arcana, system-ui, sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText('PAUSED', canvas.width / 2, canvas.height / 2 + 100);
    ctx.textAlign = 'left';
  }
}


function updateVisualHUD() {
  const levelConfig = LEVELS[currentLevel - 1];
  const heartsContainer = document.getElementById('heartsContainer');
  heartsContainer.innerHTML = '';
  for (let i = 0; i < 3; i++) {
    const heart = document.createElement('img');
    heart.src = 'assets/items/Heart.png';
    heart.className = 'heart-icon';
    heart.style.opacity = i < lives ? '1' : '0.3';
    heartsContainer.appendChild(heart);
  }

  document.getElementById('levelDisplay').textContent = `LEVEL ${currentLevel}`;
  const foodContainer = document.getElementById('foodContainer');
  foodContainer.innerHTML = '';
  const tunaIcon = document.createElement('img');
  tunaIcon.src = '/assets/items/Tuna.png';
  tunaIcon.className = 'tuna-icon';
  foodContainer.appendChild(tunaIcon);
  const foodText = document.createElement('span');
  foodText.textContent = `${eaten}/${levelConfig.food}`;
  foodContainer.appendChild(foodText);
}

function drawLevelText() {
  ctx.fillStyle = 'rgba(0,0,0,.7)';
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  switch (levelTextReason) {
    case 'gameOver':
      ctx.fillStyle = '#ff4444';
      ctx.font = 'bold 64px Arcana, system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.fillText('GAME OVER', canvas.width / 2, canvas.height / 2);
      break;
    case 'death':
      ctx.fillStyle = '#ff9068';
      ctx.font = 'bold 48px Arcana, system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.fillText('LIFE LOST!', canvas.width / 2, canvas.height / 2 - 20);
      ctx.fillStyle = '#fff';
      ctx.font = '24px Arcana, system-ui, sans-serif';
      const lifeText = lives === 1 ? 'life remaining' : 'lives remaining';
      ctx.fillText(`${lives} ${lifeText}`, canvas.width / 2, canvas.height / 2 + 30);
      break;
    case 'congratulations':
      ctx.fillStyle = '#FFD700';
      ctx.font = 'bold 48px Arcana, system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.fillText('CONGRATULATIONS!', canvas.width / 2, canvas.height / 2 - 20);
      ctx.fillStyle = '#fff';
      ctx.font = '24px Arcana, system-ui, sans-serif';
      ctx.fillText('You completed all levels!', canvas.width / 2, canvas.height / 2 + 30);
      break;
    case 'complete':
      ctx.fillStyle = '#7be065';
      ctx.font = 'bold 48px Arcana, system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.fillText('LEVEL COMPLETE!', canvas.width / 2, canvas.height / 2 - 20);
      if (currentLevel < LEVELS.length) {
        ctx.fillStyle = '#fff';
        ctx.font = '24px Arcana, system-ui, sans-serif';
        ctx.fillText(`Advancing to level ${currentLevel + 1}...`, canvas.width / 2, canvas.height / 2 + 30);
      }
      break;
    case 'start':
    default:
      ctx.fillStyle = '#7be065';
      ctx.font = 'bold 48px Arcana, system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.fillText(`LEVEL ${currentLevel}`, canvas.width / 2, canvas.height / 2);
      break;
  }
  ctx.textAlign = 'left';
}

window.addEventListener('keydown', (e) => {
  if (e.key in DIRS && !showingLevelText) {
    nextDir = DIRS[e.key];
    e.preventDefault();
  }
  else if (e.key === 'p' || e.key === 'P') {
    paused = !paused;
  }
});

function gameOver() {
  running = false;
  lives--;
  updateVisualHUD();

  if (lives <= 0) {
    gameEnded = true;
    levelTextReason = 'gameOver';
  } else {
    gameEnded = false;
    levelTextReason = 'death';
  }
  showingLevelText = true;
  levelTextStartTime = performance.now();
}

function levelComplete() {
  running = false;
  levelTextReason = 'complete';
  showingLevelText = true;
  levelTextStartTime = performance.now();
}

Promise.all([
  loadImage(ASSETS.head),
  loadImage(ASSETS.body),
  loadImage(ASSETS.tuna),
  loadImage(ASSETS.heart)
]).then(([head, body, tuna, heart]) => {
  IMG.head = head;
  IMG.body = body;
  IMG.tuna = tuna;
  IMG.heart = heart;

  ctx.imageSmoothingEnabled = false;

  initGame();
});
