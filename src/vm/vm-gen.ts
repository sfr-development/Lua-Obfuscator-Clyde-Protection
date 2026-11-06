import type { BytecodeChunk, Constant } from "./bytecode.js";
import { Lexer } from "../lexer/Lexer.js";
import { Parser } from "../parser/Parser.js";
import { compile as compileAST } from "./Compiler.js";

let _rng: () => number = Math.random;

function seedRandom(seed: number): void {
  let s = seed | 0;
  _rng = () => {
    s = (s + 0x6D2B79F5) | 0;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function rng(): number { return _rng(); }

function compileString(luaSource: string): BytecodeChunk {
  const lexer = new Lexer(luaSource);
  const { tokens, errors: lexErrors } = lexer.lex();
  if (lexErrors.length > 0) {
    throw new Error(`[compileString] Lex errors: ${lexErrors.map(e => e.message).join("; ")}`);
  }
  const parser = new Parser(tokens);
  const ast = parser.parse();
  const parseErrors = parser.getErrors();
  if (parseErrors.length > 0) {
    throw new Error(`[compileString] Parse errors: ${parseErrors.map(e => e.message).join("; ")}`);
  }
  return compileAST(ast);
}

function shuffleOpcodes(doShuffle: boolean): { encode: number[]; decode: number[] } {
  const n = 68;
  const arr = Array.from({ length: n }, (_, i) => i);
  if (doShuffle) {
    for (let i = n - 1; i > 0; i--) {
      const j = Math.floor(rng() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
  }
  const encode = new Array(n);
  const decode = new Array(n);
  for (let i = 0; i < n; i++) {
    encode[i] = arr[i];
    decode[arr[i]] = i;
  }
  return { encode, decode };
}

const OPCODES_1ARG = new Set([
  4, 5, 6, 7, 8, 30, 31, 32, 33, 34, 35, 37, 38, 40, 41, 42, 43,
  44, 45, 47, 49, 50, 52, 54, 55, 65, 67
]);

const OPCODES_2ARG = new Set([39, 53, 60, 61, 66]);

const OPCODES_3ARG = new Set([56, 57, 58, 59, 62, 63]);

function mapBytecode(code: number[], opcodeEncode: number[]): number[] {
  const result = [...code];
  let i = 0;
  while (i < result.length) {
    const op = result[i];
    if (op >= 0 && op < opcodeEncode.length) {
      result[i] = opcodeEncode[op];
    }
    i++;
    const argCount = OPCODES_3ARG.has(op) ? 3 : OPCODES_2ARG.has(op) ? 2 : OPCODES_1ARG.has(op) ? 1 : 0;
    i += argCount;
  }
  return result;
}

function collectJumpTargets(code: number[]): Set<number> {
  const targets = new Set<number>();
  let i = 0;
  while (i < code.length) {
    const op = code[i];
    i++;
    if (op === 32 || op === 33 || op === 42 || op === 43) {

      targets.add(code[i]);
      i++;
    } else if (op === 53) {

      i++;
      targets.add(code[i]);
      i++;
    } else {
      const ac = OPCODES_3ARG.has(op) ? 3 : OPCODES_2ARG.has(op) ? 2 : OPCODES_1ARG.has(op) ? 1 : 0;
      i += ac;
    }
  }
  return targets;
}

function canFuse(start: number, len: number, jumpTargets: Set<number>): boolean {
  for (let i = start + 1; i < start + len; i++) {
    if (jumpTargets.has(i)) return false;
  }
  return true;
}

function fuseOpcodes(code: number[]): number[] {
  const result = [...code];
  const jt = collectJumpTargets(code);
  let i = 0;
  while (i < result.length) {
    const op = result[i];

    if (op === 5 && i + 6 < result.length) {
      const a = result[i + 1];

      if (result[i + 2] === 5 && result[i + 5] === 6) {
        const b = result[i + 3];
        const arith = result[i + 4];
        const c = result[i + 6];
        const superOp = arith === 9 ? 57 : arith === 10 ? 58 : arith === 11 ? 59 : arith === 15 ? 63 : -1;
        if (superOp !== -1 && canFuse(i, 7, jt) && rng() > 0.25) {
          result[i] = superOp; result[i+1] = a; result[i+2] = b; result[i+3] = c;
          result[i+4] = 0; result[i+5] = 0; result[i+6] = 0;
          i += 7; continue;
        }
      }

      if (result[i + 2] === 4 && result[i + 4] === 9 && result[i + 5] === 6) {
        const k = result[i + 3];
        const c = result[i + 6];
        if (canFuse(i, 7, jt) && rng() > 0.25) {
          result[i] = 62; result[i+1] = a; result[i+2] = k; result[i+3] = c;
          result[i+4] = 0; result[i+5] = 0; result[i+6] = 0;
          i += 7; continue;
        }
      }

      if (result[i + 2] === 6) {
        const b = result[i + 3];
        if (canFuse(i, 4, jt) && rng() > 0.25) {
          result[i] = 61; result[i+1] = a; result[i+2] = b; result[i+3] = 0;
          i += 4; continue;
        }
      }
    }

    if (op === 4 && i + 3 < result.length && result[i + 2] === 6) {
      const k = result[i + 1];
      const s = result[i + 3];
      if (canFuse(i, 4, jt) && rng() > 0.25) {
        result[i] = 60; result[i+1] = k; result[i+2] = s; result[i+3] = 0;
        i += 4; continue;
      }
    }

    i++;
    const ac = OPCODES_3ARG.has(op) ? 3 : OPCODES_2ARG.has(op) ? 2 : OPCODES_1ARG.has(op) ? 1 : 0;
    i += ac;
  }
  return result;
}

function fuseChunk(chunk: BytecodeChunk): void {
  chunk.code = fuseOpcodes(chunk.code);
  if (chunk.protos) {
    for (const p of chunk.protos) fuseChunk(p);
  }
}

function injectCamouflage(code: number[]): number[] {

  const boundaries: number[] = [];
  let i = 0;
  while (i < code.length) {
    boundaries.push(i);
    const op = code[i];
    i++;
    const ac = OPCODES_3ARG.has(op) ? 3 : OPCODES_2ARG.has(op) ? 2 : OPCODES_1ARG.has(op) ? 1 : 0;
    i += ac;
  }
  boundaries.push(code.length);

  const insertions: { pos: number; bytes: number[] }[] = [];
  for (let bi = 1; bi < boundaries.length - 1; bi++) {
    if (rng() < 0.12) {
      const camoType = Math.floor(rng() * 3);
      const bytes: number[] = [64 + camoType];
      for (let a = 0; a < camoType; a++) bytes.push(Math.floor(rng() * 256));
      insertions.push({ pos: boundaries[bi], bytes });
    }
  }
  if (insertions.length === 0) return code;

  const offsets = new Array(code.length + 1).fill(0);
  let insIdx = 0;
  let cum = 0;
  for (let pos = 0; pos <= code.length; pos++) {
    while (insIdx < insertions.length && insertions[insIdx].pos === pos) {
      cum += insertions[insIdx].bytes.length;
      insIdx++;
    }
    offsets[pos] = cum;
  }

  const result: number[] = [];
  insIdx = 0;
  for (let pos = 0; pos < code.length; pos++) {
    while (insIdx < insertions.length && insertions[insIdx].pos === pos) {
      result.push(...insertions[insIdx].bytes);
      insIdx++;
    }
    result.push(code[pos]);
  }

  i = 0;
  while (i < code.length) {
    const op = code[i];
    const newI = i + offsets[i];
    if (op === 32 || op === 33 || op === 42 || op === 43) {

      const origTarget = code[i + 1];
      const safeTarget = Math.min(origTarget, code.length);
      result[newI + 1] = safeTarget + offsets[safeTarget];
    } else if (op === 53) {

      const origTarget = code[i + 2];
      const safeTarget = Math.min(origTarget, code.length);
      result[newI + 2] = safeTarget + offsets[safeTarget];
    }
    i++;
    const ac = OPCODES_3ARG.has(op) ? 3 : OPCODES_2ARG.has(op) ? 2 : OPCODES_1ARG.has(op) ? 1 : 0;
    i += ac;
  }

  return result;
}

function injectCamouflageChunk(chunk: BytecodeChunk): void {
  chunk.code = injectCamouflage(chunk.code);
  if (chunk.protos) {
    for (const p of chunk.protos) injectCamouflageChunk(p);
  }
}

function instrSize(op: number): number {
  return 1 + (OPCODES_3ARG.has(op) ? 3 : OPCODES_2ARG.has(op) ? 2 : OPCODES_1ARG.has(op) ? 1 : 0);
}

function isTerminator(op: number): boolean {
  return op === 32   || op === 31   || op === 41  ;
}

function isJumpOp(op: number): { argIdx: number } | null {
  if (op === 32 || op === 33 || op === 42 || op === 43) return { argIdx: 0 };
  if (op === 53) return { argIdx: 1 };
  return null;
}

interface BasicBlock {
  id: number;
  startPos: number;
  code: number[];
  fallsThrough: boolean;
}

function flattenBytecodeBlocks(code: number[]): number[] {
  if (code.length < 20) return code;

  const blockBoundaries = new Set<number>();
  blockBoundaries.add(0);

  let i = 0;
  while (i < code.length) {
    const op = code[i];
    const sz = instrSize(op);
    const nextI = i + sz;

    const jmp = isJumpOp(op);
    if (jmp) {
      const target = code[i + 1 + jmp.argIdx];
      if (target >= 0 && target < code.length) blockBoundaries.add(target);
      if (nextI < code.length) blockBoundaries.add(nextI);
    }
    if (op === 31 || op === 41) {
      if (nextI < code.length) blockBoundaries.add(nextI);
    }

    i = nextI;
  }

  const sortedBounds = Array.from(blockBoundaries).sort((a, b) => a - b);
  if (sortedBounds.length < 3) return code;

  const blocks: BasicBlock[] = [];
  for (let bi = 0; bi < sortedBounds.length; bi++) {
    const bStart = sortedBounds[bi];
    const bEnd = bi + 1 < sortedBounds.length ? sortedBounds[bi + 1] : code.length;
    if (bStart >= code.length || bEnd <= bStart) continue;

    const blockCode = code.slice(bStart, bEnd);

    let lastOp = -1;
    let j = 0;
    while (j < blockCode.length) {
      lastOp = blockCode[j];
      j += instrSize(lastOp);
    }
    const fallsThrough = !isTerminator(lastOp);

    blocks.push({ id: bi, startPos: bStart, code: blockCode, fallsThrough });
  }

  if (blocks.length < 3) return code;

  const nextBlockStart = new Map<number, number>();
  for (let bi = 0; bi < blocks.length - 1; bi++) {
    nextBlockStart.set(blocks[bi].startPos, blocks[bi + 1].startPos);
  }

  const entry = blocks[0];
  const rest = blocks.slice(1);
  for (let si = rest.length - 1; si > 0; si--) {
    const sj = Math.floor(rng() * (si + 1));
    [rest[si], rest[sj]] = [rest[sj], rest[si]];
  }
  const shuffled = [entry, ...rest];

  const oldStartToNewStart = new Map<number, number>();
  let pos = 0;
  for (const block of shuffled) {
    oldStartToNewStart.set(block.startPos, pos);
    pos += block.code.length;
    if (block.fallsThrough) pos += 2;
  }

  const newCode: number[] = [];
  for (const block of shuffled) {

    let j = 0;
    while (j < block.code.length) {
      const op = block.code[j];
      newCode.push(op);
      j++;
      const sz = instrSize(op) - 1;
      for (let ai = 0; ai < sz; ai++) {
        let arg = block.code[j];

        const jmpInfo = isJumpOp(op);
        if (jmpInfo && ai === jmpInfo.argIdx && oldStartToNewStart.has(arg)) {
          arg = oldStartToNewStart.get(arg)!;
        }
        newCode.push(arg);
        j++;
      }
    }

    if (block.fallsThrough) {
      const nextOldStart = nextBlockStart.get(block.startPos);
      const targetNew = nextOldStart !== undefined ? (oldStartToNewStart.get(nextOldStart) ?? newCode.length + 2) : newCode.length + 2;
      newCode.push(32);
      newCode.push(targetNew);
    }
  }

  return newCode;
}

function flattenChunk(chunk: BytecodeChunk): void {
  chunk.code = flattenBytecodeBlocks(chunk.code);
  if (chunk.protos) {
    for (const p of chunk.protos) flattenChunk(p);
  }
}

function computeCtxBit(ctxInit: number, ctxPrime: number, pos: number): number {

  const luaIp = pos + 1;
  return (((ctxInit ^ Math.imul(luaIp, ctxPrime)) >>> 0) >>> 16) & 1;
}

function contextOpcodeTransform(code: number[], ctxInit: number, ctxPrime: number): number[] {
  const result = [...code];
  let i = 0;
  while (i < result.length) {
    const op = result[i];
    const ctxBit = computeCtxBit(ctxInit, ctxPrime, i);

    if (op === 5 && ctxBit === 0 && rng() < 0.35) {
      result[i] = 67;
    } else if (op === 4 && ctxBit === 1 && rng() < 0.35) {
      result[i] = 67;
    }

    i++;
    const ac = OPCODES_3ARG.has(op) ? 3 : OPCODES_2ARG.has(op) ? 2 : OPCODES_1ARG.has(op) ? 1 : 0;
    i += ac;
  }
  return result;
}

function contextTransformChunk(chunk: BytecodeChunk, ctxInit: number, ctxPrime: number): void {
  chunk.code = contextOpcodeTransform(chunk.code, ctxInit, ctxPrime);
  if (chunk.protos) {
    for (const p of chunk.protos) contextTransformChunk(p, ctxInit, ctxPrime);
  }
}

function encodeJumpTargets(code: number[], jumpKey: number): number[] {
  const result = [...code];
  let i = 0;
  while (i < result.length) {
    const op = result[i];
    i++;
    if (op === 32 || op === 33 || op === 42 || op === 43) {

      result[i] = (result[i] ^ jumpKey) >>> 0;
      i++;
    } else if (op === 53) {

      i++;
      result[i] = (result[i] ^ jumpKey) >>> 0;
      i++;
    } else {
      const ac = OPCODES_3ARG.has(op) ? 3 : OPCODES_2ARG.has(op) ? 2 : OPCODES_1ARG.has(op) ? 1 : 0;
      i += ac;
    }
  }
  return result;
}

function encodeJumpTargetsChunk(chunk: BytecodeChunk, jumpKey: number): void {
  chunk.code = encodeJumpTargets(chunk.code, jumpKey);
  if (chunk.protos) {
    for (const p of chunk.protos) encodeJumpTargetsChunk(p, jumpKey);
  }
}

let _nameCounter = 0;

function resetNames(): void {
  _nameCounter = 0;
}

function randomName(len: number = 6): string {
  const chars = "Il1O0_";
  let name = "_";
  for (let i = 0; i < len; i++) {
    name += chars[Math.floor(rng() * chars.length)];
  }
  name += (_nameCounter++).toString(36);
  return name;
}

function toUTF8Bytes(s: string): number[] {
  const bytes: number[] = [];
  for (let i = 0; i < s.length; i++) {
    let c = s.charCodeAt(i);
    if (c < 0x80) {
      bytes.push(c);
    } else if (c < 0x800) {
      bytes.push(0xc0 | (c >> 6), 0x80 | (c & 0x3f));
    } else if (c >= 0xd800 && c <= 0xdbff && i + 1 < s.length) {
      const lo = s.charCodeAt(++i);
      c = ((c - 0xd800) << 10) + (lo - 0xdc00) + 0x10000;
      bytes.push(0xf0 | (c >> 18), 0x80 | ((c >> 12) & 0x3f), 0x80 | ((c >> 6) & 0x3f), 0x80 | (c & 0x3f));
    } else {
      bytes.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 0x3f), 0x80 | (c & 0x3f));
    }
  }
  return bytes;
}

function luaStringLiteral(s: string): string {
  const bytes = toUTF8Bytes(s);
  let out = '"';
  for (const b of bytes) {
    if (b === 34) out += '\\"';
    else if (b === 92) out += "\\\\";
    else if (b === 10) out += "\\n";
    else if (b === 13) out += "\\r";
    else if (b === 0) out += "\\000";
    else if (b < 32 || b > 126) out += `\\${b.toString().padStart(3, '0')}`;
    else out += String.fromCharCode(b);
  }
  return out + '"';
}

function toHexLit(n: number): string {
  if (!isFinite(n)) {
    if (n === Infinity) return "math.huge";
    if (n === -Infinity) return "-math.huge";
    return "(0/0)";
  }
  if (Object.is(n, -0)) return "-0x0p0";
  if (n === 0) return "0x0";

  const sign = n < 0 ? "-" : "";
  const abs = Math.abs(n);

  if (Number.isInteger(abs) && abs <= 0xFFFFFFFF) {
    return `${sign}0x${abs.toString(16)}`;
  }

  let exp = Math.floor(Math.log2(abs));
  let mant = abs / (2 ** exp);
  while (mant >= 2) { mant /= 2; exp++; }
  while (mant > 0 && mant < 1) { mant *= 2; exp--; }

  let frac = mant - 1;
  let hexDigits = "";
  for (let i = 0; i < 13; i++) {
    frac *= 16;
    const d = Math.floor(frac);
    hexDigits += d.toString(16);
    frac -= d;
    if (Math.abs(frac) < 1e-14) break;
  }
  hexDigits = hexDigits.replace(/0+$/, "");
  return hexDigits
    ? `${sign}0x1.${hexDigits}p${exp}`
    : `${sign}0x1p${exp}`;
}

function toHexInt(n: number): string {
  if (n === 0) return "0x0";
  const sign = n < 0 ? "-" : "";
  return `${sign}0x${Math.abs(n).toString(16)}`;
}

function obfuscateNumber(n: number): string {
  if (!isFinite(n) || Object.is(n, -0)) {
    if (Object.is(n, -0)) return "-0";
    if (n === Infinity) return "math.huge";
    if (n === -Infinity) return "-math.huge";
    return "0/0";
  }

  if (!Number.isInteger(n)) return String(n);

  if (n >= -1 && n <= 2) return toHexInt(n);

  const pick = Math.floor(rng() * 3);

  if (pick === 0) {

    const a = Math.floor(rng() * 10000) - 5000;
    return `(${toHexInt(a)}+${toHexInt(n - a)})`;
  }
  if (pick === 1 && n !== 0) {

    const d = 2 + Math.floor(rng() * 7);
    const r = ((n % d) + d) % d;
    const q = (n - r) / d;
    return `(${toHexInt(d)}*${toHexInt(q)}+${toHexInt(r)})`;
  }

  const a = n + 1 + Math.floor(rng() * 10000);
  return `(${toHexInt(a)}-${toHexInt(a - n)})`;
}

function encryptByte(b: number, dk: number, strategy: number): number {
  if (strategy === 0) return b ^ dk;
  if (strategy === 1) return (b + dk) & 0xFF;
  if (strategy === 2) return b ^ (((dk << 3) | (dk >>> 5)) & 0xFF);
  return (b + (dk ^ 0xAA)) & 0xFF;
}

function encryptStringLazy(bytes: number[], idx1: number, baseKey: number, keyPrime: number, doMutation: boolean = false): number[] {
  let key = ((baseKey ^ Math.imul(idx1, keyPrime)) >>> 0);

  const strategy = doMutation ? ((key >>> 16) & 3) : 0;
  const result: number[] = [];
  for (let j = 0; j < bytes.length; j++) {
    const dk = key & 0xFF;
    const encrypted = encryptByte(bytes[j], dk, strategy);
    result.push(encrypted);
    key = ((key ^ bytes[j]) >>> 0);
    key = (((key << 7) | (key >>> 25)) >>> 0);
  }
  return result;
}

function encryptStringFragment(bytes: number[], idx1: number, baseKey: number, keyPrime: number, doMutation: boolean = false): number[] {

  const fragSize = doMutation ? (2 + Math.floor(rng() * 5)) : (2 + Math.floor(rng() * 3));
  const nRealFrags = Math.ceil(bytes.length / fragSize);

  const padded = [...bytes];
  while (padded.length < nRealFrags * fragSize) padded.push(0);

  const nFakes = doMutation
    ? Math.max(1, Math.floor(nRealFrags * (0.30 + rng() * 0.20)))
    : Math.max(1, Math.floor(nRealFrags * (0.25 + rng() * 0.10)));
  const totalFrags = nRealFrags + nFakes;

  const allPos: number[] = [];
  for (let i = 1; i <= totalFrags; i++) allPos.push(i);
  for (let i = allPos.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [allPos[i], allPos[j]] = [allPos[j], allPos[i]];
  }
  const perm = allPos.slice(0, nRealFrags);

  const data = new Array(totalFrags * fragSize);
  for (let i = 0; i < data.length; i++) data[i] = Math.floor(rng() * 256);

  let key = ((baseKey ^ Math.imul(idx1, keyPrime)) >>> 0);
  const strategy = doMutation ? ((key >>> 16) & 3) : 0;

  for (let fi = 0; fi < nRealFrags; fi++) {
    const storagePos = perm[fi];
    const dataOffset = (storagePos - 1) * fragSize;
    for (let bi = 0; bi < fragSize; bi++) {
      const origByte = padded[fi * fragSize + bi];
      const dk = key & 0xFF;
      data[dataOffset + bi] = encryptByte(origByte, dk, strategy);
      key = ((key ^ origByte) >>> 0);
      key = (((key << 7) | (key >>> 25)) >>> 0);
    }
  }

  const result: number[] = [];
  result.push(-nRealFrags);
  result.push(fragSize);
  result.push(totalFrags);
  result.push(bytes.length);
  for (const p of perm) result.push(p);
  for (const d of data) result.push(d);
  return result;
}

function buildStringPools(
  K: (Constant | any)[],
  lazyBaseKey: number,
  lazyKeyPrime: number,
  doMutation: boolean,
): { processedK: any[]; pools: number[][] } {
  const nPools = 2 + Math.floor(rng() * 3);
  const pools: number[][] = [];
  for (let i = 0; i < nPools; i++) {

    const junk: number[] = [];
    for (let j = 0; j < 2 + Math.floor(rng() * 5); j++) junk.push(Math.floor(rng() * 256));
    pools.push(junk);
  }

  const processedK: any[] = [...K];

  for (let i = 0; i < K.length; i++) {
    if (typeof K[i] !== "string") continue;
    const str = K[i] as string;
    if (str.length === 0) continue;

    const bytes = toUTF8Bytes(str);
    const idx1 = i + 1;

    const encrypted = encryptStringLazy(bytes, idx1, lazyBaseKey, lazyKeyPrime, doMutation);

    const poolIdx = Math.floor(rng() * nPools);

    for (let j = 0; j < 1 + Math.floor(rng() * 6); j++) pools[poolIdx].push(Math.floor(rng() * 256));

    const offset = pools[poolIdx].length + 1;

    for (const b of encrypted) pools[poolIdx].push(b);

    for (let j = 0; j < 1 + Math.floor(rng() * 6); j++) pools[poolIdx].push(Math.floor(rng() * 256));

    processedK[i] = { __recipe: true, poolIdx: poolIdx + 1, offset, len: bytes.length };
  }

  return { processedK, pools };
}

function serializeConstant(v: Constant, encodeStrings: boolean, xorKey: number = 0, doFragment: boolean = false, xorStep: number = 0, stringIndex: number = 0, doConstantFold: boolean = false, lazyBaseKey: number = 0, lazyKeyPrime: number = 0, doMutation: boolean = false): string {
  if (v === null || v === undefined) return "nil";
  if (typeof v === "boolean") return v ? "true" : "false";
  if (typeof v === "number") {
    if (Object.is(v, -0)) return "-0";
    if (!isFinite(v)) {
      if (v === Infinity) return "math.huge";
      if (v === -Infinity) return "-math.huge";
      return "0/0";
    }

    if (lazyBaseKey && Number.isInteger(v) && v >= 0 && v <= 0x7FFFFFFF && rng() < 0.3) {
      const mask = 1 + Math.floor(rng() * 0x7FFE);
      const masked = v ^ mask;
      return `{-999,${masked},${mask}}`;
    }
    return doConstantFold ? obfuscateNumber(v) : String(v);
  }

  if (typeof v === "object" && v !== null && typeof v !== "string" && (v as any).__recipe) {
    const r = v as any;
    const pi = doConstantFold ? obfuscateNumber(r.poolIdx) : String(r.poolIdx);
    const off = doConstantFold ? obfuscateNumber(r.offset) : String(r.offset);
    const ln = doConstantFold ? obfuscateNumber(r.len) : String(r.len);
    return `{-998,${pi},${off},${ln}}`;
  }
  if (typeof v === "string") {
    if (encodeStrings) {
      const bytes = toUTF8Bytes(v);
      if (lazyBaseKey) {
        const idx1 = stringIndex + 1;
        if (bytes.length > 4) {

          const fragData = encryptStringFragment(bytes, idx1, lazyBaseKey, lazyKeyPrime, doMutation);
          return `{${fragData.join(",")}}`;
        }

        const encrypted = encryptStringLazy(bytes, idx1, lazyBaseKey, lazyKeyPrime, doMutation);
        return `{${encrypted.join(",")}}`;
      }

      const xored = bytes.map((b, i) => {
        const key = (xorKey + i * xorStep + stringIndex) & 0xFF;
        return b ^ key;
      });

      if (doFragment && xored.length > 3 && rng() > 0.3) {
        const nFrags = 2 + Math.floor(rng() * 2);
        const fragSize = Math.ceil(xored.length / nFrags);
        const frags: string[] = [];
        for (let fi = 0; fi < xored.length; fi += fragSize) {
          frags.push(`{${xored.slice(fi, fi + fragSize).join(",")}}`);
        }
        return `{${frags.join(",")}}`;
      }
      return `{${xored.join(",")}}`;
    } else {
      return luaStringLiteral(v);
    }
  }
  return "nil";
}

function serializeConstants(K: Constant[], encodeStrings: boolean, xorKey: number = 0, doFragment: boolean = false, xorStep: number = 0, doConstantFold: boolean = false, lazyBaseKey: number = 0, lazyKeyPrime: number = 0, doMutation: boolean = false): string {
  return `{${K.map((v, idx) => serializeConstant(v, encodeStrings, xorKey, doFragment, xorStep, idx, doConstantFold, lazyBaseKey, lazyKeyPrime, doMutation)).join(",")}}`;
}

function lzssCompress(input: number[]): number[] {
  const out: number[] = [];
  const WIN = 4096;
  const MIN_MATCH = 3;
  const MAX_MATCH = 18;
  const HASH_SIZE = 1 << 16;
  const HASH_MASK = HASH_SIZE - 1;

  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(input.length).fill(-1);

  function hash3(pos: number): number {
    return ((input[pos] << 10) ^ (input[pos+1] << 5) ^ input[pos+2]) & HASH_MASK;
  }

  let i = 0;
  while (i < input.length) {
    let flagByte = 0;
    const flagPos = out.length;
    out.push(0);
    for (let bit = 0; bit < 8 && i < input.length; bit++) {
      let bestLen = 0, bestOff = 0;
      if (i + 2 < input.length) {
        const h = hash3(i);
        let j = head[h];
        const limit = Math.max(0, i - WIN);
        let chain = 0;
        while (j >= limit && chain < 48) {
          let len = 0;
          while (len < MAX_MATCH && i + len < input.length && input[j + len] === input[i + len]) len++;
          if (len > bestLen) { bestLen = len; bestOff = i - j; }
          if (len === MAX_MATCH) break;
          j = prev[j];
          if (j < 0) break;
          chain++;
        }
        prev[i] = head[h];
        head[h] = i;
      }
      if (bestLen >= MIN_MATCH) {
        const encoded = ((bestOff - 1) << 4) | (bestLen - MIN_MATCH);
        out.push((encoded >> 8) & 0xFF);
        out.push(encoded & 0xFF);
        for (let s = 1; s < bestLen && i + s + 2 < input.length; s++) {
          const sh = hash3(i + s);
          prev[i + s] = head[sh];
          head[sh] = i + s;
        }
        i += bestLen;
      } else {
        flagByte |= (1 << bit);
        out.push(input[i]);
        i++;
      }
    }
    out[flagPos] = flagByte;
  }
  return out;
}

function rleCompress(input: number[]): number[] {
  const out: number[] = [];

  let i = 0;
  while (i < input.length) {
    const b = input[i];
    let run = 1;
    while (i + run < input.length && input[i + run] === b && run < 258) run++;
    if (run >= 4) {
      out.push(0xFF, run - 3, b);
      i += run;
    } else if (b === 0xFF) {
      out.push(0xFF, 0x00);
      i++;
    } else {
      out.push(b);
      i++;
    }
  }
  return out;
}

function b64Encode(bytes: number[]): string {
  const chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  let out = "";
  for (let i = 0; i < bytes.length; i += 3) {
    const b0 = bytes[i], b1 = bytes[i + 1] ?? 0, b2 = bytes[i + 2] ?? 0;
    out += chars[(b0 >> 2) & 0x3F];
    out += chars[((b0 << 4) | (b1 >> 4)) & 0x3F];
    out += (i + 1 < bytes.length) ? chars[((b1 << 2) | (b2 >> 6)) & 0x3F] : "=";
    out += (i + 2 < bytes.length) ? chars[b2 & 0x3F] : "=";
  }
  return out;
}

function wrapCustomCipher(source: string): string {

  const srcBytes: number[] = [];
  for (let i = 0; i < source.length; i++) srcBytes.push(source.charCodeAt(i));

  const sbox: number[] = Array.from({length: 256}, (_, i) => i);
  for (let i = 255; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [sbox[i], sbox[j]] = [sbox[j], sbox[i]];
  }

  const isbox: number[] = new Array(256);
  for (let i = 0; i < 256; i++) isbox[sbox[i]] = i;

  const posSeed = (Math.floor(rng() * 254) + 1) & 0xFF;
  const posStep = (Math.floor(rng() * 30) + 3) & 0xFF;

  const prefixLen = 16 + Math.floor(rng() * 49);
  const plainBytes: number[] = [prefixLen];
  for (let i = 0; i < prefixLen; i++) plainBytes.push(Math.floor(rng() * 256));
  for (let i = 0; i < srcBytes.length; i++) plainBytes.push(srcBytes[i]);

  const encrypted: number[] = [];
  let pk = posSeed;
  for (let i = 0; i < plainBytes.length; i++) {
    const xored = (plainBytes[i] ^ pk) & 0xFF;
    encrypted.push(sbox[xored]);
    pk = (pk + posStep) & 0xFF;
  }

  const stdAlpha = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  const alphaArr = stdAlpha.split('');
  for (let i = alphaArr.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [alphaArr[i], alphaArr[j]] = [alphaArr[j], alphaArr[i]];
  }
  const cipherAlpha = alphaArr.join('');

  let encoded = "";
  for (let i = 0; i < encrypted.length; i += 3) {
    const b0 = encrypted[i], b1 = encrypted[i + 1] ?? 0, b2 = encrypted[i + 2] ?? 0;
    encoded += cipherAlpha[(b0 >> 2) & 0x3F];
    encoded += cipherAlpha[((b0 << 4) | (b1 >> 4)) & 0x3F];
    encoded += (i + 1 < encrypted.length) ? cipherAlpha[((b1 << 2) | (b2 >> 6)) & 0x3F] : "=";
    encoded += (i + 2 < encrypted.length) ? cipherAlpha[b2 & 0x3F] : "=";
  }

  const nFrags = 3 + Math.floor(rng() * 3);
  const fragSz = Math.ceil(encoded.length / nFrags);
  const frags: string[] = [];
  for (let i = 0; i < nFrags; i++) frags.push(encoded.slice(i * fragSz, (i + 1) * fragSz));

  const isboxChunks: string[] = [];
  const chunkSz = 64;
  for (let i = 0; i < 256; i += chunkSz) {
    isboxChunks.push(isbox.slice(i, i + chunkSz).join(","));
  }

  const vSc = randomName(3);
  const vSb = randomName(3);
  const vEnv = randomName(2);
  const vTc = randomName(3);
  const vLd = randomName(3);
  const vAlpha = randomName(4);
  const vLut = randomName(3);
  const vSbox = randomName(3);
  const vFt = randomName(3);
  const vData = randomName(3);
  const vDec = randomName(3);
  const vOut = randomName(3);
  const vPk = randomName(2);
  const vB32 = randomName(3);

  function junkLine(): string {
    const jv = randomName(2);
    const variants = [
      `local ${jv}=${Math.floor(rng() * 9999)}`,
      `local ${jv}={}`,
      `local ${jv}="${randomName(6)}"`,
      `local ${jv}=nil`,
      `local ${jv}=true`,
      `local ${jv}=#"${randomName(3)}"`,
      `local ${jv}=(function() return ${Math.floor(rng() * 999)} end)()`,
    ];
    return variants[Math.floor(rng() * variants.length)];
  }

  function maybeJunk(lines: string[]): void {
    if (rng() > 0.4) {
      const n = 1 + Math.floor(rng() * 3);
      for (let i = 0; i < n; i++) lines.push(junkLine());
    }
  }

  const lines: string[] = [];

  const bootVariant = Math.floor(rng() * 3);
  if (bootVariant === 0) {

    lines.push(`local ${vSc}=("")[("\\99\\104\\97\\114")]`);
    lines.push(`local ${vSb}=("")[("\\98\\121\\116\\101")]`);
  } else if (bootVariant === 1) {

    const _mt = randomName(2);
    lines.push(`local ${_mt}=("")[("\\114\\101\\112")]`);
    lines.push(`local ${vSc}=("")[("\\99\\104\\97\\114")]`);
    lines.push(`local ${vSb}=("")[("\\98\\121\\116\\101")]`);
  } else {

    lines.push(`local ${vSb}=("")[("\\98\\121\\116\\101")]`);
    lines.push(`local ${vSc}=("")[("\\99\\104\\97\\114")]`);
  }
  maybeJunk(lines);

  const envVariant = 0;
  lines.push(`local ${vEnv}=(type(getfenv)=="function" and getfenv(0) or _G)`);

  const builtinLines: string[] = [
    `local ${vTc}=${vEnv}[${vSc}(116,97,98,108,101)][${vSc}(99,111,110,99,97,116)]`,
    `local ${vLd}=${vEnv}[${vSc}(108,111,97,100,115,116,114,105,110,103)] or ${vEnv}[${vSc}(108,111,97,100)]`,
    `local ${vB32}=${vEnv}[${vSc}(98,105,116,51,50)]`,
  ];

  for (let i = builtinLines.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [builtinLines[i], builtinLines[j]] = [builtinLines[j], builtinLines[i]];
  }
  for (const bl of builtinLines) {
    lines.push(bl);
    if (rng() > 0.6) lines.push(junkLine());
  }
  maybeJunk(lines);

  const buildLut = (): string[] => {
    const l: string[] = [];
    l.push(`local ${vAlpha}="${cipherAlpha}"`);
    l.push(`local ${vLut}={}`);

    const lutLoopVar = Math.floor(rng() * 2);
    if (lutLoopVar === 0) {
      l.push(`for _i=1,64 do ${vLut}[${vSb}(${vAlpha},_i)]=_i-1 end`);
    } else {
      const _n = randomName(2);
      l.push(`local ${_n}=#${vAlpha}`);
      l.push(`for _i=1,${_n} do ${vLut}[${vSb}(${vAlpha},_i)]=_i-1 end`);
    }
    return l;
  };

  const buildSbox = (): string[] => {
    const l: string[] = [];
    l.push(`local ${vSbox}={}`);
    const chunkOrder = [0, 1, 2, 3];
    for (let i = chunkOrder.length - 1; i > 0; i--) {
      const j = Math.floor(rng() * (i + 1));
      [chunkOrder[i], chunkOrder[j]] = [chunkOrder[j], chunkOrder[i]];
    }

    const chunkStyle = Math.floor(rng() * 2);
    for (const ci of chunkOrder) {
      const offset = ci * chunkSz;
      if (chunkStyle === 0) {
        l.push(`do local _t={${isboxChunks[ci]}} for _i=1,${chunkSz} do ${vSbox}[${offset}+_i-1]=_t[_i] end end`);
      } else {

        const vals = isbox.slice(ci * chunkSz, (ci + 1) * chunkSz);
        const assignments: string[] = [];
        for (let vi = 0; vi < vals.length; vi++) {
          assignments.push(`${vSbox}[${offset + vi}]=${vals[vi]}`);
        }

        const batchSz = 8 + Math.floor(rng() * 9);
        for (let bi = 0; bi < assignments.length; bi += batchSz) {
          l.push(assignments.slice(bi, bi + batchSz).join("\n"));
        }
      }
      if (rng() > 0.7) l.push(junkLine());
    }
    return l;
  };

  const buildFrags = (): string[] => {
    const l: string[] = [];
    const fragStyle = Math.floor(rng() * 2);
    if (fragStyle === 0) {

      l.push(`local ${vFt}={}`);
      const declOrder = Array.from({length: nFrags}, (_, i) => i);
      for (let i = declOrder.length - 1; i > 0; i--) {
        const j = Math.floor(rng() * (i + 1));
        [declOrder[i], declOrder[j]] = [declOrder[j], declOrder[i]];
      }
      for (const idx of declOrder) {
        l.push(`${vFt}[${idx + 1}]="${frags[idx]}"`);
        if (rng() > 0.8) l.push(junkLine());
      }
      l.push(`local ${vData}=${vTc}(${vFt})`);
    } else {

      const fragVars: string[] = [];
      const declOrder = Array.from({length: nFrags}, (_, i) => i);
      for (let i = declOrder.length - 1; i > 0; i--) {
        const j = Math.floor(rng() * (i + 1));
        [declOrder[i], declOrder[j]] = [declOrder[j], declOrder[i]];
      }
      for (const idx of declOrder) {
        const fv = randomName(3);
        fragVars[idx] = fv;
        l.push(`local ${fv}="${frags[idx]}"`);
        if (rng() > 0.8) l.push(junkLine());
      }
      l.push(`local ${vData}=${fragVars.join("..")}`);
    }
    return l;
  };

  const sections: Array<() => string[]> = [buildLut, buildSbox, buildFrags];
  for (let i = sections.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [sections[i], sections[j]] = [sections[j], sections[i]];
  }
  for (const buildSection of sections) {
    lines.push(...buildSection());
    maybeJunk(lines);
  }

  maybeJunk(lines);
  const b64Variant = Math.floor(rng() * 2);
  lines.push(`local ${vDec}={}`);
  if (b64Variant === 0) {

    const _li = randomName(2);
    lines.push(`for ${_li}=1,#${vData},4 do`);
    lines.push(`local _a,_b,_c,_d=${vLut}[${vSb}(${vData},${_li})],${vLut}[${vSb}(${vData},${_li}+1)],${vLut}[${vSb}(${vData},${_li}+2)],${vLut}[${vSb}(${vData},${_li}+3)]`);
    lines.push(`${vDec}[#${vDec}+1]=${vB32}.bor(${vB32}.lshift(_a,2),${vB32}.rshift(_b,4))`);
    lines.push(`if _c then ${vDec}[#${vDec}+1]=${vB32}.band(${vB32}.bor(${vB32}.lshift(_b,4),${vB32}.rshift(_c,2)),0xFF) end`);
    lines.push(`if _d then ${vDec}[#${vDec}+1]=${vB32}.band(${vB32}.bor(${vB32}.lshift(_c,6),_d),0xFF) end`);
    lines.push(`end`);
  } else {

    const _li = randomName(2);
    const _n = randomName(2);
    lines.push(`local ${_n}=0`);
    lines.push(`for ${_li}=1,#${vData},4 do`);
    lines.push(`local _a,_b,_c,_d=${vLut}[${vSb}(${vData},${_li})],${vLut}[${vSb}(${vData},${_li}+1)],${vLut}[${vSb}(${vData},${_li}+2)],${vLut}[${vSb}(${vData},${_li}+3)]`);
    lines.push(`${_n}=${_n}+1`);
    lines.push(`${vDec}[${_n}]=${vB32}.bor(${vB32}.lshift(_a,2),${vB32}.rshift(_b,4))`);
    lines.push(`if _c then ${_n}=${_n}+1 ${vDec}[${_n}]=${vB32}.band(${vB32}.bor(${vB32}.lshift(_b,4),${vB32}.rshift(_c,2)),0xFF) end`);
    lines.push(`if _d then ${_n}=${_n}+1 ${vDec}[${_n}]=${vB32}.band(${vB32}.bor(${vB32}.lshift(_c,6),_d),0xFF) end`);
    lines.push(`end`);
  }

  maybeJunk(lines);
  const decryptVariant = Math.floor(rng() * 2);
  lines.push(`local ${vOut}={}`);
  lines.push(`local ${vPk}=${posSeed}`);
  if (decryptVariant === 0) {
    const _li = randomName(2);
    lines.push(`for ${_li}=1,#${vDec} do`);
    lines.push(`${vOut}[${_li}]=${vSc}(${vB32}.bxor(${vSbox}[${vDec}[${_li}]],${vPk}))`);
    lines.push(`${vPk}=${vB32}.band(${vPk}+${posStep},0xFF)`);
    lines.push(`end`);
  } else {

    const _tmp = randomName(3);
    const _li = randomName(2);
    lines.push(`local ${_tmp}={}`);
    lines.push(`for ${_li}=1,#${vDec} do`);
    lines.push(`${_tmp}[${_li}]=${vB32}.bxor(${vSbox}[${vDec}[${_li}]],${vPk})`);
    lines.push(`${vPk}=${vB32}.band(${vPk}+${posStep},0xFF)`);
    lines.push(`end`);
    maybeJunk(lines);
    const _li2 = randomName(2);
    lines.push(`for ${_li2}=1,#${_tmp} do ${vOut}[${_li2}]=${vSc}(${_tmp}[${_li2}]) end`);
  }

  maybeJunk(lines);

  const vSkip = randomName(2);
  const vReal = randomName(3);
  const _liS = randomName(2);
  lines.push(`local ${vSkip}=${vSb}(${vOut}[1],1)+1`);
  lines.push(`local ${vReal}={}`);
  lines.push(`for ${_liS}=${vSkip}+1,#${vOut} do ${vReal}[#${vReal}+1]=${vOut}[${_liS}] end`);
  maybeJunk(lines);
  const execVariant = Math.floor(rng() * 3);
  if (execVariant === 0) {
    lines.push(`(${vLd}(${vTc}(${vReal})))()`);
  } else if (execVariant === 1) {
    const _fn = randomName(3);
    lines.push(`local ${_fn}=${vLd}(${vTc}(${vReal}))`);
    lines.push(`${_fn}()`);
  } else {
    const _src = randomName(3);
    const _fn = randomName(3);
    lines.push(`local ${_src}=${vTc}(${vReal})`);
    lines.push(`local ${_fn}=${vLd}(${_src})`);
    lines.push(`${_fn}()`);
  }

  console.log(`[cipher] S-Box layer: ${srcBytes.length}+${prefixLen}pfx → ${encoded.length} chars (${nFrags} frags, boot:v${bootVariant} env:v${envVariant} b64:v${b64Variant} dec:v${decryptVariant} exec:v${execVariant})`);
  return lines.join("\n");
}

function wrapNestedVM(source: string): string {
  const srcBytes: number[] = [];
  for (let i = 0; i < source.length; i++) srcBytes.push(source.charCodeAt(i));

  const prefixLen = 20 + Math.floor(rng() * 44);
  const plainBytes: number[] = [prefixLen & 0xFF];
  for (let i = 0; i < prefixLen; i++) plainBytes.push(Math.floor(rng() * 256));
  for (const b of srcBytes) plainBytes.push(b);

  const nKeys = 2 + Math.floor(rng() * 2);
  const xKeys: number[] = [], xSteps: number[] = [];
  for (let i = 0; i < nKeys; i++) {
    xKeys.push((Math.floor(rng() * 254) + 1) & 0xFF);
    xSteps.push((Math.floor(rng() * 30) + 3) & 0xFF);
  }
  const afterXor: number[] = [];
  const rk = [...xKeys];
  for (let i = 0; i < plainBytes.length; i++) {
    let b = plainBytes[i];
    for (let k = 0; k < nKeys; k++) {
      b = (b ^ rk[k]) & 0xFF;
      rk[k] = (rk[k] + xSteps[k]) & 0xFF;
    }
    afterXor.push(b);
  }

  const rotKey = (Math.floor(rng() * 200) + 10) & 0xFF;
  const encBytes: number[] = afterXor.map(b => (b + rotKey) & 0xFF);

  const stdAlpha = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  const alphaArr = stdAlpha.split('');
  for (let i = alphaArr.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [alphaArr[i], alphaArr[j]] = [alphaArr[j], alphaArr[i]];
  }
  const alpha = alphaArr.join('');

  let encoded = "";
  for (let i = 0; i < encBytes.length; i += 3) {
    const b0 = encBytes[i], b1 = encBytes[i + 1] ?? 0, b2 = encBytes[i + 2] ?? 0;
    encoded += alpha[(b0 >> 2) & 0x3F];
    encoded += alpha[((b0 << 4) | (b1 >> 4)) & 0x3F];
    encoded += (i + 1 < encBytes.length) ? alpha[((b1 << 2) | (b2 >> 6)) & 0x3F] : "=";
    encoded += (i + 2 < encBytes.length) ? alpha[b2 & 0x3F] : "=";
  }

  const nAlphaFrags = 6 + Math.floor(rng() * 3);
  const alphaFragSz = Math.ceil(64 / nAlphaFrags);
  const alphaFragKeys: number[] = [];
  const alphaFragData: number[][] = [];
  for (let i = 0; i < nAlphaFrags; i++) {
    const fk = (Math.floor(rng() * 254) + 1) & 0xFF;
    alphaFragKeys.push(fk);
    const start = i * alphaFragSz;
    const end = Math.min((i + 1) * alphaFragSz, 64);
    const piece = alpha.slice(start, end);
    alphaFragData.push(Array.from(piece).map(c => (c.charCodeAt(0) ^ fk) & 0xFF));
  }

  const nDataFrags = 5 + Math.floor(rng() * 4);
  const dataFragSz = Math.ceil(encoded.length / nDataFrags);
  const dataFrags: string[] = [];
  for (let i = 0; i < nDataFrags; i++) dataFrags.push(encoded.slice(i * dataFragSz, (i + 1) * dataFragSz));

  const nn = (len = 4) => randomName(len);
  const vSc = nn(3), vSb = nn(3);
  const vEnv = nn(3), vTc = nn(3), vLd = nn(3), vB32 = nn(3);
  const vBxor = nn(3), vBand = nn(3), vBor = nn(3), vLsh = nn(3), vRsh = nn(3);
  const vAlpha = nn(4), vLut = nn(3);
  const vData = nn(3), vDec = nn(3), vOut = nn(3);

  const rInt = (): string => {
    const v = Math.floor(rng() * 0xFFFF);
    const fmt = Math.floor(rng() * 4);
    if (fmt === 0) return `0x${v.toString(16).toUpperCase()}`;
    if (fmt === 1) return `0b${v.toString(2)}`;
    if (fmt === 2) return `${Math.floor(v/1000)}_${String(v%1000).padStart(3,'0')}`;
    return `${v}`;
  };

  const rSpecStr = (): string => {
    const chars = '!@#$%^&*()_+-=[]{}|;:<>?,./~`';
    const len = 3 + Math.floor(rng() * 8);
    return Array.from({length: len}, () => chars[Math.floor(rng() * chars.length)]).join('');
  };

  const emitHoneypot = (): string => {
    const hv1 = nn(2), hv2 = nn(2);
    const variant = Math.floor(rng() * 14);
    switch (variant) {
      case 0: return `local ${hv1}=${rInt()} while true do ${hv1}=${vBxor}(${hv1},${rInt()}) break end`;
      case 1: return `do local ${hv1}=${rInt()} if ${hv1}>${rInt()} then ${hv1}=${hv1}-${rInt()} else ${hv1}=${hv1}+${rInt()} end end`;
      case 2: return `local ${hv1}=${rInt()} local ${hv2}=0 repeat ${hv1}=(${hv1}+${rInt()})%65536 ${hv2}=${hv2}+1 until ${hv2}>=${2+Math.floor(rng()*4)}`;
      case 3: return `local ${hv1}={${Array.from({length:3+Math.floor(rng()*5)},()=>rInt()).join(',')}} do local ${hv2}=0 for _=1,#${hv1} do ${hv2}=${hv2}+${hv1}[_] end end`;
      case 4: return `local ${hv1}="${rSpecStr()}" local ${hv2}=0 for _=1,#${hv1} do ${hv2}=${vBxor}(${hv2},${vSb}(${hv1},_)) end`;
      case 5: return `do local ${hv1}=${rInt()} for ${hv2}=1,${2+Math.floor(rng()*4)} do ${hv1}=(${hv1}*3+${hv2})%0x10000 end end`;
      case 6: return `local ${hv1}=${rInt()} if ${hv1}>${rInt()} then while true do ${hv1}=${vBand}(${hv1},${rInt()}) break end else ${hv1}=${vBor}(${hv1},${rInt()}) end`;
      case 7: return `local ${hv1}=${rInt()} local ${hv2}=${rInt()} if ${hv1}<${hv2} then ${hv1}=${hv2}-${hv1} else ${hv2}=${hv1}-${hv2} end ${hv1}=(${hv1}+${hv2})%65536`;
      case 8: return `do local ${hv1}="${rSpecStr()}" local ${hv2}=${rInt()} for _=1,#${hv1} do ${hv2}=(${hv2}+${vSb}(${hv1},_))%0x10000 end end`;
      case 9: return `local ${hv1}={} for ${hv2}=1,${2+Math.floor(rng()*3)} do ${hv1}[${hv2}]=${vBxor}(${rInt()},${hv2}) end`;
      case 10: {
        const d = 2+Math.floor(rng()*3);
        let s = `local ${hv1}=${rInt()} `;
        for(let i=0;i<d;i++) s += `if ${hv1}>${rInt()} then ${hv1}=${hv1}-${rInt()} else `;
        s += `${hv1}=${hv1}+${rInt()} `;
        for(let i=0;i<d;i++) s += `end `;
        return s;
      }
      case 11: return `local ${hv1}=(function() local ${hv2}=${rInt()} while true do ${hv2}=${vBxor}(${hv2},${rInt()}) break end return ${hv2} end)()`;
      case 12: return `do local ${hv1}=${rInt()} while true do if ${hv1}>${rInt()} then ${hv1}=${vBand}(${hv1},${rInt()}) end break end end`;
      case 13: return `local ${hv1}=${rInt()} for ${hv2}=1,${1+Math.floor(rng()*3)} do if ${hv2}%2==0 then ${hv1}=${vBxor}(${hv1},${hv2}) else ${hv1}=${vBand}(${hv1}+${hv2},0xFFFF) end end`;
      default: return `local ${hv1}=${rInt()}`;
    }
  };

  const opaquePred = (): string => {
    const preds = [
      `type("")=="string"`, `type(1)=="number"`, `type({})=="table"`,
      `1+1==2`, `#""==0`, `type(true)=="boolean"`, `not(1>2)`,
    ];
    return preds[Math.floor(rng() * preds.length)];
  };

  const encSC = (s: string) => Array.from(s).map(c => c.charCodeAt(0)).join(',');

  const L: string[] = [];

  const bootV = Math.floor(rng() * 3);
  if (bootV === 0) {
    L.push(`local ${vSc}=("")[("\\99\\104\\97\\114")]`);
    L.push(`local ${vSb}=("")[("\\98\\121\\116\\101")]`);
  } else if (bootV === 1) {
    L.push(`local ${vSb}=("")[("\\98\\121\\116\\101")]`);
    L.push(`local ${vSc}=("")[("\\99\\104\\97\\114")]`);
  } else {
    const mt = nn(2);
    L.push(`local ${mt}=("")[("\\115\\117\\98")]`);
    L.push(`local ${vSc}=("")[("\\99\\104\\97\\114")]`);
    L.push(`local ${vSb}=("")[("\\98\\121\\116\\101")]`);
  }
  L.push(emitHoneypot());

  L.push(`local ${vEnv}=(type(getfenv)=="function" and getfenv(0) or _G)`);
  const builtins = [
    `local ${vTc}=${vEnv}[${vSc}(${encSC('table')})][${vSc}(${encSC('concat')})]`,
    `local ${vLd}=${vEnv}[${vSc}(${encSC('loadstring')})] or ${vEnv}[${vSc}(${encSC('load')})]`,
    `local ${vB32}=${vEnv}[${vSc}(${encSC('bit32')})]`,
  ];
  for (let i = builtins.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [builtins[i], builtins[j]] = [builtins[j], builtins[i]];
  }
  for (const bl of builtins) {
    L.push(bl);
    if (rng() > 0.6) L.push(emitHoneypot());
  }
  const b32methods: [string, string][] = [
    [vBxor, 'bxor'], [vBand, 'band'], [vBor, 'bor'], [vLsh, 'lshift'], [vRsh, 'rshift']
  ];
  for (let i = b32methods.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [b32methods[i], b32methods[j]] = [b32methods[j], b32methods[i]];
  }
  for (const [v, name] of b32methods) L.push(`local ${v}=${vB32}[${vSc}(${encSC(name)})]`);
  L.push(emitHoneypot());
  L.push(emitHoneypot());

  const alphaFragVars: string[] = [];
  for (let i = 0; i < nAlphaFrags; i++) alphaFragVars.push(nn(3));
  const alphaOrder = Array.from({length: nAlphaFrags}, (_, i) => i);
  for (let i = alphaOrder.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [alphaOrder[i], alphaOrder[j]] = [alphaOrder[j], alphaOrder[i]];
  }
  L.push(emitHoneypot());
  for (const idx of alphaOrder) {
    L.push(`local ${alphaFragVars[idx]}={${alphaFragData[idx].join(',')}}`);
    if (rng() > 0.5) L.push(emitHoneypot());
  }

  L.push(`local ${vAlpha}=""`);
  for (let i = 0; i < nAlphaFrags; i++) {
    const lv = nn(2);
    if (rng() > 0.5) {
      L.push(`if ${opaquePred()} then for ${lv}=1,#${alphaFragVars[i]} do ${vAlpha}=${vAlpha}..${vSc}(${vBxor}(${alphaFragVars[i]}[${lv}],${alphaFragKeys[i]})) end end`);
    } else {
      L.push(`for ${lv}=1,#${alphaFragVars[i]} do ${vAlpha}=${vAlpha}..${vSc}(${vBxor}(${alphaFragVars[i]}[${lv}],${alphaFragKeys[i]})) end`);
    }
    if (rng() > 0.65) L.push(emitHoneypot());
  }

  L.push(`local ${vLut}={}`);
  const lutV = nn(2);
  L.push(`for ${lutV}=1,#${vAlpha} do ${vLut}[${vSb}(${vAlpha},${lutV})]=${lutV}-1 end`);
  L.push(emitHoneypot());

  const dataFragVars: string[] = [];
  for (let i = 0; i < nDataFrags; i++) dataFragVars.push(nn(3));
  const dataOrder = Array.from({length: nDataFrags}, (_, i) => i);
  for (let i = dataOrder.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [dataOrder[i], dataOrder[j]] = [dataOrder[j], dataOrder[i]];
  }
  for (const idx of dataOrder) {
    L.push(`local ${dataFragVars[idx]}="${dataFrags[idx]}"`);
    if (rng() > 0.65) L.push(emitHoneypot());
  }

  const concatV = Math.floor(rng() * 2);
  if (concatV === 0) {
    L.push(`local ${vData}=${dataFragVars.join('..')}`);
  } else {
    const tbl = nn(3);
    L.push(`local ${tbl}={${dataFragVars.join(',')}}`);
    L.push(`local ${vData}=${vTc}(${tbl})`);
  }
  L.push(emitHoneypot());

  L.push(`local ${vDec}={}`);
  const b64Li = nn(2);
  const b64V = Math.floor(rng() * 2);
  if (b64V === 0) {
    L.push(`for ${b64Li}=1,#${vData},4 do`);
    L.push(`local _a,_b,_c,_d=${vLut}[${vSb}(${vData},${b64Li})],${vLut}[${vSb}(${vData},${b64Li}+1)],${vLut}[${vSb}(${vData},${b64Li}+2)],${vLut}[${vSb}(${vData},${b64Li}+3)]`);
    L.push(`${vDec}[#${vDec}+1]=${vBor}(${vLsh}(_a,2),${vRsh}(_b,4))`);
    L.push(`if _c then ${vDec}[#${vDec}+1]=${vBand}(${vBor}(${vLsh}(_b,4),${vRsh}(_c,2)),0xFF) end`);
    L.push(`if _d then ${vDec}[#${vDec}+1]=${vBand}(${vBor}(${vLsh}(_c,6),_d),0xFF) end`);
    L.push(`end`);
  } else {
    const cnt = nn(2);
    L.push(`local ${cnt}=0`);
    L.push(`for ${b64Li}=1,#${vData},4 do`);
    L.push(`local _a,_b,_c,_d=${vLut}[${vSb}(${vData},${b64Li})],${vLut}[${vSb}(${vData},${b64Li}+1)],${vLut}[${vSb}(${vData},${b64Li}+2)],${vLut}[${vSb}(${vData},${b64Li}+3)]`);
    L.push(`${cnt}=${cnt}+1 ${vDec}[${cnt}]=${vBor}(${vLsh}(_a,2),${vRsh}(_b,4))`);
    L.push(`if _c then ${cnt}=${cnt}+1 ${vDec}[${cnt}]=${vBand}(${vBor}(${vLsh}(_b,4),${vRsh}(_c,2)),0xFF) end`);
    L.push(`if _d then ${cnt}=${cnt}+1 ${vDec}[${cnt}]=${vBand}(${vBor}(${vLsh}(_c,6),_d),0xFF) end`);
    L.push(`end`);
  }
  L.push(emitHoneypot());

  const rotLi = nn(2);

  const rotKv = nn(3);
  const rotBase = Math.floor(rng() * 200);
  const rotDelta = rotKey - rotBase;
  if (rng() > 0.5) {
    L.push(`local ${rotKv}=${rotBase} ${rotKv}=${rotKv}+${rotDelta}`);
  } else {
    const rotA = nn(2), rotB = nn(2);
    const a = Math.floor(rng() * 200) + 50, b = rotKey - a;
    L.push(`local ${rotA}=${a} local ${rotB}=${b < 0 ? '(0-' + (-b) + ')' : String(b)}`);
    L.push(`local ${rotKv}=${rotA}+${rotB}`);
  }
  L.push(`for ${rotLi}=1,#${vDec} do ${vDec}[${rotLi}]=${vBand}(${vDec}[${rotLi}]-${rotKv}+256,0xFF) end`);
  L.push(emitHoneypot());

  for (let k = 0; k < nKeys; k++) {
    const rkVar = nn(2), decLi = nn(2);

    const kBase = Math.floor(rng() * 100);
    const kDelta = xKeys[k] - kBase;
    if (rng() > 0.5) {
      L.push(`do local ${rkVar}=${kBase}+${kDelta}`);
    } else {
      const kMul = 2 + Math.floor(rng() * 5);
      const kSrc = Math.floor(xKeys[k] / kMul);
      const kRem = xKeys[k] - kSrc * kMul;
      L.push(`do local ${rkVar}=${kSrc}*${kMul}+${kRem}`);
    }
    L.push(`for ${decLi}=1,#${vDec} do ${vDec}[${decLi}]=${vBxor}(${vDec}[${decLi}],${rkVar}) ${rkVar}=${vBand}(${rkVar}+${xSteps[k]},0xFF) end`);
    L.push(`end`);
    if (rng() > 0.4) L.push(emitHoneypot());
  }

  L.push(emitHoneypot());
  const vSkip = nn(2);
  L.push(`local ${vSkip}=${vDec}[1]+1`);
  L.push(`local ${vOut}={}`);
  const sLi = nn(2);
  L.push(`for ${sLi}=${vSkip}+1,#${vDec} do ${vOut}[#${vOut}+1]=${vSc}(${vDec}[${sLi}]) end`);
  L.push(emitHoneypot());

  const execV = Math.floor(rng() * 3);
  if (execV === 0) {
    L.push(`(${vLd}(${vTc}(${vOut})))()`);
  } else if (execV === 1) {
    const fn = nn(3);
    L.push(`local ${fn}=${vLd}(${vTc}(${vOut}))`);
    L.push(`${fn}()`);
  } else {
    const srcV = nn(3), fn = nn(3);
    L.push(`local ${srcV}=${vTc}(${vOut})`);
    L.push(`local ${fn}=${vLd}(${srcV})`);
    L.push(`${fn}()`);
  }

  console.log(`[nested] Multi-key(${nKeys}) + rot(${rotKey}) layer: ${srcBytes.length}+${prefixLen}pfx → ${encoded.length} chars (${nAlphaFrags} alpha frags, ${nDataFrags} data frags)`);
  return L.join("\n");
}

function wrapStubVM(source: string): string {
  const srcBytes: number[] = [];
  for (let i = 0; i < source.length; i++) srcBytes.push(source.charCodeAt(i));

  const compressed = lzssCompress(srcBytes);
  const ratio = ((1 - compressed.length / srcBytes.length) * 100).toFixed(1);

  const stdAlpha = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  const aa = stdAlpha.split('');
  for (let i = aa.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [aa[i], aa[j]] = [aa[j], aa[i]];
  }
  const shuffledAlpha = aa.join('');

  const encVariant = Math.floor(rng() * 4);
  const keyDerivVariant = Math.floor(rng() * 4);
  let stubKey = 0;
  for (let i = 0; i < shuffledAlpha.length; i++) {
    const b = shuffledAlpha.charCodeAt(i);
    if (keyDerivVariant === 0) stubKey = (stubKey ^ b) & 0xFF;
    else if (keyDerivVariant === 1) stubKey = (stubKey + b) & 0xFF;
    else if (keyDerivVariant === 2) stubKey = ((stubKey * 31 + b) & 0xFF) | 0;
    else stubKey = (i & 1) === 0 ? ((stubKey ^ b) & 0xFF) : ((stubKey + b) & 0xFF);
  }
  stubKey = stubKey || 1;
  const rollingStep = (Math.floor(rng() * 30) + 3) & 0xFF;
  const encrypted: number[] = [];
  let rk = stubKey;
  for (let i = 0; i < compressed.length; i++) {
    const b = compressed[i];
    if (encVariant === 0) encrypted.push((b ^ stubKey) & 0xFF);
    else if (encVariant === 1) encrypted.push((b + stubKey) & 0xFF);
    else if (encVariant === 2) encrypted.push((256 + b - stubKey) & 0xFF);
    else { encrypted.push((b ^ rk) & 0xFF); rk = (rk + rollingStep) & 0xFF; }
  }

  let encoded = "";
  for (let i = 0; i < encrypted.length; i += 3) {
    const b0 = encrypted[i], b1 = encrypted[i+1] ?? 0, b2 = encrypted[i+2] ?? 0;
    encoded += shuffledAlpha[(b0 >> 2) & 0x3F];
    encoded += shuffledAlpha[((b0 << 4) | (b1 >> 4)) & 0x3F];
    encoded += (i+1 < encrypted.length) ? shuffledAlpha[((b1 << 2) | (b2 >> 6)) & 0x3F] : "=";
    encoded += (i+2 < encrypted.length) ? shuffledAlpha[b2 & 0x3F] : "=";
  }

  const nFrags = 3 + Math.floor(rng() * 3);
  const fragSz = Math.ceil(encoded.length / nFrags);
  const frags: string[] = [];
  for (let i = 0; i < nFrags; i++) frags.push(encoded.slice(i * fragSz, (i+1) * fragSz));

  const expectedLen = srcBytes.length;

  console.log(`[stub] LZSS: ${srcBytes.length} → ${compressed.length} (${ratio}%) | enc:v${encVariant} | frags:${nFrags}`);
  console.log(`[stub] Encoded: ${encoded.length} chars | ~${((encoded.length + 2500) / 1024).toFixed(0)}KB`);

  const n = (len = 4) => randomName(len);
  const a_sc = n(), a_sb = n(), a_bx = n(), a_ba = n(), a_bo = n(), a_bl = n(), a_br = n();
  const a_tc = n(), a_ls = n(), a_d = n(), a_o = n(), a_t = n();
  const b32v = n(), efv = n(3), pvv = n(3);
  const a_lut = n(), a_abc = n(), a_ft = n(), a_s = n();
  const fragVars = frags.map(() => n());
  const fk1 = n(), fk2 = n(), fk3 = n(), fk4 = n(), fk5 = n();
  const cv = n(3);

  const bootVariant = [0, 2, 3][Math.floor(rng() * 3)];
  const combineVariant = Math.floor(rng() * 3);
  const shiftVariant = Math.floor(rng() * 2);
  console.log(`[stub] polymorphism: boot:${bootVariant} combine:${combineVariant} shift:${shiftVariant} keyDeriv:${keyDerivVariant}`);

  const encStr = (s: string): string =>
    Array.from(s).map(c => { const v = c.charCodeAt(0); return rng() > 0.5 ? `\\${v.toString().padStart(3,'0')}` : `\\${v}`; }).join('');
  const encSC = (s: string): string =>
    Array.from(s).map(c => c.charCodeAt(0)).join(',');

  const L: string[] = [];

  if (bootVariant === 0) {

    L.push(`local ${a_sc}=("")[("${encStr('char')}")]`);
    L.push(`local ${a_sb}=("")[("${encStr('byte')}")]`);
  } else if (bootVariant === 2) {

    const pf1 = n(3), pf2 = n(3);
    L.push(`local ${pf1},${a_sc}=pcall(function() return ("")[("${encStr('char')}")]end)`);
    L.push(`local ${pf2},${a_sb}=pcall(function() return ("")[("${encStr('byte')}")]end)`);
  } else {

    const tv = n(3);
    L.push(`local ${tv}={"\\0"}`);
    L.push(`local ${a_sc}=${tv}[1][("${encStr('char')}")]`);
    L.push(`local ${a_sb}=${tv}[1][("${encStr('byte')}")]`);
  }

  L.push(`local ${pvv},${efv}=pcall(getfenv,0)`);
  L.push(`if not ${pvv} then ${efv}=_G end`);

  L.push(`local ${b32v}=${efv}[${a_sc}(${encSC('bit32')})]`);
  const b32Methods: [string, string][] = [
    [a_bx, 'bxor'], [a_ba, 'band'], [a_bo, 'bor'], [a_bl, 'lshift'], [a_br, 'rshift']
  ];
  for (let i = b32Methods.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [b32Methods[i], b32Methods[j]] = [b32Methods[j], b32Methods[i]];
  }
  for (const [v, name] of b32Methods) L.push(`local ${v}=${b32v}[${a_sc}(${encSC(name)})]`);
  L.push(`local ${a_tc}=${efv}[${a_sc}(${encSC('table')})][${a_sc}(${encSC('concat')})]`);
  L.push(`local ${a_ls}=${efv}[${a_sc}(${encSC('loadstring')})]or ${efv}[${a_sc}(${encSC('load')})]`);

  const sigVar = n(3);
  const tsVar = n(3);
  L.push(`local ${tsVar}=${efv}[${a_sc}(${encSC('tostring')})]`);
  L.push(`local ${sigVar}=${tsVar}(${a_ls})`);

  const safeBaitChars = '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ!#$%&()*+,-./:;<=>?@[]^_`{|}~';
  const fakeBait = Array.from({length: 48}, () => safeBaitChars[Math.floor(rng() * safeBaitChars.length)]).join('');
  const fakeCheck1 = Math.floor(rng() * 0xFFFFFF);
  L.push(`local ${fk1}="${fakeBait}"`);
  L.push(`local ${fk2}={}`);
  L.push(`for _i=1,#${fk1} do ${fk2}[_i]=${a_bx}(${a_sb}(${fk1},_i),${a_ba}(_i,0xFF)) end`);
  L.push(`local ${fk3}=0`);
  L.push(`for _i=1,#${fk2} do ${fk3}=${fk3}+${fk2}[_i] end`);
  L.push(`if ${fk3}==0x${fakeCheck1.toString(16)} then ${a_ls}(${a_tc}(${fk2}))() return end`);

  const declOrder = Array.from({length: nFrags}, (_, i) => i);
  for (let i = declOrder.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [declOrder[i], declOrder[j]] = [declOrder[j], declOrder[i]];
  }
  for (const idx of declOrder) {
    L.push(`local ${fragVars[idx]}="${frags[idx]}"`);
  }

  const fakeCheck2 = Math.floor(rng() * 0xFFFFFF);
  L.push(`local ${fk4}=0`);
  L.push(`for _i=1,#${fragVars[0]} do ${fk4}=${a_bx}(${fk4},${a_sb}(${fragVars[0]},_i)) end`);
  L.push(`if ${fk4}==0x${fakeCheck2.toString(16)} then local _z={} for _i=1,#${fragVars[0]} do _z[_i]=${a_sc}(${a_ba}(${a_sb}(${fragVars[0]},_i),0x7F)) end ${a_ls}(${a_tc}(_z))() return end`);

  L.push(`local ${a_s}=${fragVars.join('..')}`);

  const alphaXorKey = 1 + Math.floor(rng() * 254);
  const nAlphaPieces = 3 + Math.floor(rng() * 3);
  const alphaPieceSize = Math.ceil(64 / nAlphaPieces);
  const alphaPieceVars: string[] = [];

  const alphaOrder = Array.from({length: nAlphaPieces}, (_, i) => i);
  for (let i = alphaOrder.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [alphaOrder[i], alphaOrder[j]] = [alphaOrder[j], alphaOrder[i]];
  }
  for (let p = 0; p < nAlphaPieces; p++) alphaPieceVars.push(n());
  for (const p of alphaOrder) {
    const piece = shuffledAlpha.slice(p * alphaPieceSize, (p + 1) * alphaPieceSize);
    const encrypted = Array.from(piece).map(c => (c.charCodeAt(0) ^ alphaXorKey) & 0xFF);
    L.push(`local ${alphaPieceVars[p]}={${encrypted.join(',')}}`);
  }

  L.push(`local ${a_abc}=""`);
  for (let p = 0; p < nAlphaPieces; p++) {
    L.push(`for _i=1,#${alphaPieceVars[p]} do ${a_abc}=${a_abc}..${a_sc}(${a_bx}(${alphaPieceVars[p]}[_i],${alphaXorKey})) end`);
  }

  L.push(`local ${a_lut}={}`);
  L.push(`for _i=1,#${a_abc} do ${a_lut}[${a_sb}(${a_abc},_i)]=_i-1 end`);

  L.push(`local ${a_d}={}`);

  const kv = n(3);
  const keyTableVar = n(3);
  const keyTableLen = 8 + Math.floor(rng() * 8);
  const keyTableBytes: number[] = [];
  let xorAcc = 0;
  for (let i = 0; i < keyTableLen - 1; i++) {
    const b = Math.floor(rng() * 256);
    keyTableBytes.push(b);
    xorAcc = (xorAcc ^ b) & 0xFF;
  }
  keyTableBytes.push((xorAcc ^ stubKey) & 0xFF);
  L.push(`local ${keyTableVar}={${keyTableBytes.join(',')}}`);
  L.push(`local ${kv}=0 for _i=1,#${keyTableVar} do ${kv}=${a_bx}(${kv},${keyTableVar}[_i]) end`);
  L.push(`${kv}=${a_ba}(${kv},0xFF)`);
  L.push(`if ${kv}==0 then ${kv}=1 end`);
  if (encVariant === 3) {
    L.push(`local _dk=${kv}`);
    L.push(`local _ds=${rollingStep}`);
  }

  L.push(`for _i=1,#${a_s},4 do`);
  L.push(`local _a,_b2,_c,_e=${a_sb}(${a_s},_i,_i+3)`);
  L.push(`_a=${a_lut}[_a]or 0`);
  L.push(`_b2=${a_lut}[_b2]or 0`);
  L.push(`_c=${a_lut}[_c]or 0`);
  L.push(`_e=${a_lut}[_e]or 0`);

  const shl = (x: string, amt: number): string =>
    shiftVariant === 0 ? `${a_bl}(${x},${amt})` : `(${x}*${1 << amt})`;
  const combine = (x: string, y: string): string => {
    if (combineVariant === 0) return `${a_bo}(${x},${y})`;
    if (combineVariant === 1) return `(${x}+${y})`;
    return `${a_bx}(${x},${y})`;
  };
  const b1 = `${a_ba}(${combine(shl('_a',2),`${a_br}(_b2,4)`)},0xFF)`;
  const b2 = `${a_ba}(${combine(shl('_b2',4),`${a_br}(_c,2)`)},0xFF)`;
  const b3 = `${a_ba}(${combine(shl('_c',6),'_e')},0xFF)`;

  const dk = (expr: string): string => {
    if (encVariant === 0) return `${a_bx}(${expr},${kv})`;
    if (encVariant === 1) return `${a_ba}((${expr}-${kv}+256),0xFF)`;
    if (encVariant === 2) return `${a_ba}((${expr}+${kv}),0xFF)`;
    return `${a_bx}(${expr},_dk)`;
  };

  if (encVariant === 3) {

    L.push(`${a_d}[#${a_d}+1]=${dk(b1)} _dk=${a_ba}((_dk+_ds),0xFF)`);
    L.push(`if ${a_sb}(${a_s},_i+2)~=61 then ${a_d}[#${a_d}+1]=${dk(b2)} _dk=${a_ba}((_dk+_ds),0xFF) end`);
    L.push(`if ${a_sb}(${a_s},_i+3)~=61 then ${a_d}[#${a_d}+1]=${dk(b3)} _dk=${a_ba}((_dk+_ds),0xFF) end`);
  } else {
    L.push(`${a_d}[#${a_d}+1]=${dk(b1)}`);
    L.push(`if ${a_sb}(${a_s},_i+2)~=61 then ${a_d}[#${a_d}+1]=${dk(b2)} end`);
    L.push(`if ${a_sb}(${a_s},_i+3)~=61 then ${a_d}[#${a_d}+1]=${dk(b3)} end`);
  }
  L.push(`end`);

  const lzssVariant = Math.floor(rng() * 3);
  const encVariant2 = Math.floor(rng() * 3);
  const useCounter = rng() > 0.5;

  const _lp = n(3), _lf = n(3), _lb = n(2), _lm = n(2), _lc = n(3);
  const _lv = n(3), _loff = n(2), _lln = n(2), _lj = n(2), _lsz = n(2);

  L.push(`local ${a_o}={}`);
  L.push(`local ${_lp}=1`);
  if (useCounter) L.push(`local ${_lc}=0`);

  L.push(`while ${_lp}<=#${a_d} do`);
  L.push(`local ${_lf}=${a_d}[${_lp}]`);
  L.push(`${_lp}=${_lp}+1`);

  if (lzssVariant === 0) {
    L.push(`for ${_lb}=0,7 do`);
  } else if (lzssVariant === 1) {
    L.push(`local ${_lb}=0`);
    L.push(`local ${_lm}=1`);
    L.push(`while ${_lb}<8 do`);
  } else {
    L.push(`local ${_lb}=0`);
    L.push(`repeat`);
  }

  L.push(`if ${_lp}>#${a_d} then break end`);

  if (lzssVariant === 1) {

    L.push(`if ${a_ba}(${_lf},${_lm})~=0 then`);
  } else if (rng() > 0.5) {

    L.push(`if ${a_ba}(${_lf},${a_bl}(1,${_lb}))~=0 then`);
  } else {

    L.push(`if ${a_ba}(${a_br}(${_lf},${_lb}),1)==1 then`);
  }

  if (useCounter) {
    L.push(`${_lc}=${_lc}+1`);
    L.push(`${a_o}[${_lc}]=${a_d}[${_lp}]`);
  } else {
    L.push(`${a_o}[#${a_o}+1]=${a_d}[${_lp}]`);
  }
  L.push(`${_lp}=${_lp}+1`);
  L.push(`else`);

  if (encVariant2 === 0) {
    L.push(`local ${_lv}=${a_d}[${_lp}]*256+${a_d}[${_lp}+1]`);
  } else if (encVariant2 === 1) {
    L.push(`local ${_lv}=${a_bo}(${a_bl}(${a_d}[${_lp}],8),${a_d}[${_lp}+1])`);
  } else {
    L.push(`local ${_lv}=${a_bl}(${a_d}[${_lp}],8)+${a_d}[${_lp}+1]`);
  }
  L.push(`${_lp}=${_lp}+2`);
  L.push(`local ${_loff}=${a_br}(${_lv},4)+1`);
  L.push(`local ${_lln}=${a_ba}(${_lv},0xF)+3`);

  if (useCounter) {
    const _lbase = n(2);
    L.push(`local ${_lbase}=${_lc}`);
    L.push(`for ${_lj}=1,${_lln} do ${_lc}=${_lc}+1;${a_o}[${_lc}]=${a_o}[${_lbase}-${_loff}+${_lj}] end`);
  } else {
    L.push(`local ${_lsz}=#${a_o}`);
    L.push(`for ${_lj}=1,${_lln} do ${a_o}[#${a_o}+1]=${a_o}[${_lsz}-${_loff}+${_lj}] end`);
  }

  L.push(`end`);

  if (lzssVariant === 0) {
    L.push(`end end`);
  } else if (lzssVariant === 1) {
    L.push(`${_lm}=${_lm}*2`);
    L.push(`${_lb}=${_lb}+1`);
    L.push(`end end`);
  } else {
    L.push(`${_lb}=${_lb}+1`);
    L.push(`until ${_lb}>=8`);
    L.push(`end`);
  }
  console.log(`[stub] lzss_decoder: loop:v${lzssVariant} enc:v${encVariant2} counter:${useCounter}`);

  const fakeCheck3 = Math.floor(rng() * 0x7FFFFFFF);
  L.push(`if #${a_o}~=${expectedLen} then local ${fk5}={} for _i=1,#${a_o} do ${fk5}[_i]=${a_sc}(${a_ba}(${a_bx}(${a_o}[_i],_i),0x7F)+1) end ${a_ls}(${a_tc}(${fk5}))() return end`);

  const ahOk = n(3);
  const ahDet = n(3);
  L.push(`local ${ahDet}=0`);

  L.push(`do local ${ahOk}=pcall(function() if ${tsVar}(${a_ls})~=${sigVar} then ${ahDet}=${ahDet}+1 end end) end`);

  const testVal = Math.floor(rng() * 900) + 100;
  const testCode = `return ${testVal}`;
  const testCodeEnc = Array.from(testCode).map(c => c.charCodeAt(0)).join(',');
  L.push(`do local ${ahOk}=pcall(function() local _f=${a_ls}(${a_sc}(${testCodeEnc}));if not _f or _f()~=${testVal} then ${ahDet}=${ahDet}+1 end end) end`);

  L.push(`if ${ahDet}>1 then return end`);

  L.push(`local ${a_t}={}`);
  L.push(`for _i=1,#${a_o} do ${a_t}[_i]=${a_sc}(${a_o}[_i]) end`);
  L.push(`${a_ls}(${a_tc}(${a_t}))()`);

  return L.join(' ');
}

function vleEncode(values: number[]): number[] {
  const bytes: number[] = [];
  for (let vi = 0; vi < values.length; vi++) {
    const v = values[vi];
    if (v === -1) {
      bytes.push(0xFF);
    } else if (v < 128) {
      bytes.push(v);
    } else if (v < 16384) {
      bytes.push(0x80 | (v >> 8));
      bytes.push(v & 0xFF);
    } else if (v < 4194304) {
      bytes.push(0xC0 | ((v >> 16) & 0x3F));
      bytes.push((v >> 8) & 0xFF);
      bytes.push(v & 0xFF);
    } else {
      bytes.push(0xE0 | ((v >> 24) & 0x1F));
      bytes.push((v >> 16) & 0xFF);
      bytes.push((v >> 8) & 0xFF);
      bytes.push(v & 0xFF);
    }
  }
  return bytes;
}

function multiLayerEncrypt(bytes: number[], seed1: number, seed2: number, seed3: number): number[] {
  const data = [...bytes];
  const len = data.length;

  let cs = seed1;
  for (let i = 0; i < len; i++) {
    data[i] = (data[i] ^ (cs & 0xFF)) & 0xFF;
    if (cs % 2 === 0) cs = (cs >>> 1);
    else cs = ((cs * 3 + 1) & 0x7FFFFFFF);
    if (cs <= 1) cs = ((seed1 ^ (i + 1)) | 2) >>> 0;
  }

  let ka = seed2 & 0xFF;
  let kb = (seed2 >> 8) & 0xFF;
  for (let i = 0; i < len; i++) {
    data[i] = (data[i] + ka) & 0xFF;
    const tmp = (ka + kb) & 0xFF;
    ka = kb;
    kb = tmp;
  }

  let prev = seed3 & 0xFF;
  for (let i = 0; i < len; i++) {
    data[i] = (data[i] ^ prev) & 0xFF;
    prev = data[i];
  }
  return data;
}

function bytesToLuaString(bytes: number[]): string {
  return '"' + bytes.map(b => {

    if (rng() < 0.5) return '\\' + b.toString().padStart(3, '0');
    return '\\' + b.toString().padStart(3, '0');
  }).join('') + '"';
}

function packCodeToTable(code: number[], seed1: number, seed2: number, seed3: number): string {
  const vle = vleEncode(code);
  const encrypted = multiLayerEncrypt(vle, seed1, seed2, seed3);
  return bytesToLuaString(encrypted);
}

function serializeCode(code: number[], codeXorKey: number = 0): string {
  if (codeXorKey) {

    return `{${code.map(v => v >= 0 ? (v ^ codeXorKey) : v).join(",")}}`;
  }
  return `{${code.join(",")}}`;
}

function serializeProtos(
  protos: BytecodeChunk[] | undefined,
  opcodeEncode: number[],
  encodeStrings: boolean,
  doShuffle: boolean,
  xorKey: number = 0,
  doFragment: boolean = false,
  xorStep: number = 0,
  codeXorKey: number = 0,
  doConstantFold: boolean = false,
  lazyBaseKey: number = 0,
  lazyKeyPrime: number = 0,
  addFakeProtos: boolean = false,
  protoKeys: { pK: string; pC: string; pP: string; pU: string; pN: string } = { pK: "K", pC: "C", pP: "P", pU: "U", pN: "nParams" },
  cipherSeeds?: [number, number, number],
  doMutation: boolean = false
): string {
  if (!protos || protos.length === 0) {
    if (!addFakeProtos) return "{}";
  }
  const items: string[] = [];
  if (protos) {
    for (const p of protos) {
      const mappedCode = doShuffle ? mapBytecode(p.code, opcodeEncode) : p.code;
      const K = serializeConstants(p.K, encodeStrings, xorKey, doFragment, xorStep, doConstantFold, lazyBaseKey, lazyKeyPrime, doMutation);

      const C = cipherSeeds
        ? packCodeToTable(mappedCode, cipherSeeds[0], cipherSeeds[1], cipherSeeds[2])
        : serializeCode(mappedCode, codeXorKey);
      const P = serializeProtos(p.protos, opcodeEncode, encodeStrings, doShuffle, xorKey, doFragment, xorStep, codeXorKey, doConstantFold, lazyBaseKey, lazyKeyPrime, false, protoKeys, cipherSeeds, doMutation);
      let U = "nil";
      if (p.upvalues && p.upvalues.length > 0) {
        U = `{${p.upvalues.map(uv => `{${uv[0]},${uv[1]}}`).join(",")}}`;
      }
      const nParams = (p as any).nParams ?? 0;
      items.push(`{${protoKeys.pK}=${K},${protoKeys.pC}=${C},${protoKeys.pP}=${P},${protoKeys.pU}=${U},${protoKeys.pN}=${nParams}}`);
    }
  }

  if (addFakeProtos) {
    const nFakes = 2 + Math.floor(rng() * 4);
    for (let fi = 0; fi < nFakes; fi++) {
      const fakeKLen = 1 + Math.floor(rng() * 5);
      const fakeK: string[] = [];
      for (let ki = 0; ki < fakeKLen; ki++) {
        const t = Math.floor(rng() * 3);
        if (t === 0) fakeK.push(String(Math.floor(rng() * 1000)));
        else if (t === 1) fakeK.push(rng() > 0.5 ? "true" : "false");
        else fakeK.push(`{${Array.from({length: 3 + Math.floor(rng() * 5)}, () => Math.floor(rng() * 256)).join(",")}}`);
      }

      let fakeC: string;
      if (cipherSeeds) {
        const fakeCLen = 4 + Math.floor(rng() * 12);
        fakeC = `{${Array.from({length: fakeCLen}, () => Math.floor(rng() * 256)).join(",")}}`;
      } else {
        const fakeCLen = 4 + Math.floor(rng() * 12);
        fakeC = `{${Array.from({length: fakeCLen}, () => Math.floor(rng() * 67)).join(",")}}`;
      }
      const fakeNParams = Math.floor(rng() * 4);
      items.push(`{${protoKeys.pK}={${fakeK.join(",")}},${protoKeys.pC}=${fakeC},${protoKeys.pP}={},${protoKeys.pU}=nil,${protoKeys.pN}=${fakeNParams}}`);
    }
  }

  return `{${items.join(",")}}`;
}

const CORE_GLOBALS = [
  "print", "warn", "error", "assert", "type", "typeof", "tostring", "tonumber",
  "pcall", "xpcall", "select", "unpack", "pairs", "ipairs", "next",
  "rawget", "rawset", "rawequal", "rawlen", "setmetatable", "getmetatable",
  "string", "table", "math", "bit32", "coroutine", "os", "debug", "utf8", "buffer",
  "game", "workspace", "script", "Instance",
  "Vector3", "Vector2", "CFrame", "Color3", "BrickColor", "UDim", "UDim2",
  "Enum", "Ray", "Region3", "Rect", "TweenInfo",
  "NumberSequence", "ColorSequence", "NumberRange", "Random", "DateTime",
  "RaycastParams", "OverlapParams",
  "tick", "time", "wait", "task", "spawn", "delay",
  "require", "loadstring", "load", "getfenv", "setfenv", "newproxy",
  "_G", "shared", "settings", "stats", "UserSettings", "version",
];

const EXECUTOR_GLOBALS = [
  "getgenv", "getrenv", "getsenv", "getrawmetatable", "setrawmetatable",
  "hookfunction", "hookmetamethod", "newcclosure", "iscclosure", "islclosure",
  "checkcaller", "cloneref", "getconnections", "firesignal",
  "getgc", "getinstances", "getnilinstances", "getscripts", "getrunningscripts",
  "getloadedmodules", "getcallingscript",
  "readfile", "writefile", "appendfile", "loadfile", "listfiles", "isfile", "isfolder",
  "makefolder", "delfolder", "delfile",
  "setclipboard", "queue_on_teleport",
  "setthreadidentity", "getthreadidentity",
  "getnamecallmethod", "setnamecallmethod",
  "isreadonly", "setreadonly", "identifyexecutor",
  "request", "syn", "Drawing", "crypt", "base64", "http",
];

function luaEsc(s: string): string {
  return '"' + Array.from(s).map(c => {
    const code = c.charCodeAt(0);
    const style = Math.floor(rng() * 3);
    if (style === 0) return '\\' + code.toString().padStart(3, '0');
    if (style === 1) return '\\' + code;
    return '\\' + code.toString().padStart(3, '0');
  }).join('') + '"';
}

function collatzKeyStream(seed: number, len: number): number[] {
  const keys: number[] = [];
  let n = seed;
  for (let i = 0; i < len; i++) {
    keys.push(n & 0xFF);
    if (n % 2 === 0) n = (n >>> 1);
    else n = (((n * 3) + 1) & 0x7FFFFFFF);
    if (n <= 1) n = ((seed ^ (i + 1)) | 2) >>> 0;
  }
  return keys;
}

function collatzEncodeString(s: string, seed: number): number[] {
  const keys = collatzKeyStream(seed, s.length);
  return Array.from(s).map((c, i) => c.charCodeAt(0) ^ keys[i]);
}

function buildEnvSetup(
  n: NameMap,
  level: VMGenLevel,
  includeExecutor: boolean
): string {
  const genv = n.genv;
  const env = n.env;

  if (level === "debug") {
    let code = `local ${genv}=(type(getgenv)=="function" and getgenv())or(type(getfenv)=="function" and getfenv(0))or _G\n`;
    const entries = CORE_GLOBALS.map(g => `${g}=${g}`).join(",");
    code += `local ${env}=setmetatable({${entries}},{__index=function(_,k) local ok,v=pcall(function() return ${genv}[k] end);if ok then return v end;return nil end})\n`;
    if (includeExecutor) {
      for (const g of EXECUTOR_GLOBALS) {
        code += `do local ok,v=pcall(function() return ${genv}["${g}"] end);if ok and v~=nil then ${env}["${g}"]=v end end\n`;
      }
    }
    return code;
  }

  const lines: string[] = [];
  const collatzSeed = (Math.floor(rng() * 0x3FFFFFFE) + 3) >>> 0;

  const bSC = randomName(3);
  const bBX = randomName(3);
  const bBA = randomName(3);
  const bBR = randomName(3);
  const bTC = randomName(3);
  const bPC = randomName(3);
  const bTY = randomName(3);
  const bSM = randomName(3);
  const bRG = randomName(3);
  const bRS = randomName(3);
  const bLS = randomName(3);

  const charCodesXor = (s: string): { codes: string; key: number } => {
    const key = 1 + Math.floor(rng() * 254);
    return { codes: Array.from(s).map(c => (c.charCodeAt(0) + key) % 256).join(","), key };
  };

  lines.push(`local ${bSC}=(${luaEsc("")})[${luaEsc("char")}]`);

  const _ldFunc = randomName(3);
  const _lsChars = Array.from("loadstring").map(c => c.charCodeAt(0));
  const _ldChars = Array.from("load").map(c => c.charCodeAt(0));
  const _lsKey = 1 + Math.floor(rng() * 254);
  const _lsEnc = _lsChars.map(c => (c + _lsKey) % 256);
  const _ldEnc = _ldChars.map(c => (c + _lsKey) % 256);
  const _tmpN = randomName(2);

  lines.push(`local ${_ldFunc}=(function() local ${_tmpN}=${luaEsc("")};for _,_c in ipairs({${_lsEnc.join(",")}}) do ${_tmpN}=${_tmpN}..${bSC}((_c-${_lsKey}+256)%256) end;local _f=(type(getfenv)=="function" and getfenv(0) or _G)[${_tmpN}];if _f then return _f end;${_tmpN}=${luaEsc("")};for _,_c in ipairs({${_ldEnc.join(",")}}) do ${_tmpN}=${_tmpN}..${bSC}((_c-${_lsKey}+256)%256) end;return (type(getfenv)=="function" and getfenv(0) or _G)[${_tmpN}] end)()`);
  lines.push(`local ${bLS}=${_ldFunc}`);

  const _resolver = randomName(4);
  const _xArr = randomName(2);
  const _xKey = randomName(2);
  lines.push(`local function ${_resolver}(${_xArr},${_xKey}) local _n=${luaEsc("")};for _i=1,#${_xArr} do _n=_n..${bSC}((${_xArr}[_i]-${_xKey}+256)%256) end;return ${_ldFunc}(${luaEsc("return ")}.._n)() end`);

  const resolveGlobal = (name: string, local_: string): string => {
    const { codes, key } = charCodesXor(name);
    return `local ${local_}=${_resolver}({${codes}},${key})`;
  };
  const resolveMethod = (lib: string, method: string, local_: string): string => {
    const { codes, key } = charCodesXor(lib);
    const _t = randomName(2);
    return `do local ${_t}=${_resolver}({${codes}},${key});${local_}=${_t}[${luaEsc(method)}] end`;
  };

  const bootstrapAssigns: string[] = [
    resolveMethod("bit32", "bxor", bBX),
    resolveMethod("bit32", "band", bBA),
    resolveMethod("bit32", "rshift", bBR),
    resolveMethod("table", "concat", bTC),
    resolveGlobal("pcall", bPC),
    resolveGlobal("type", bTY),
    resolveGlobal("setmetatable", bSM),
    resolveGlobal("rawget", bRG),
    resolveGlobal("rawset", bRS),
  ];
  for (let si = bootstrapAssigns.length - 1; si > 0; si--) {
    const sj = Math.floor(rng() * (si + 1));
    [bootstrapAssigns[si], bootstrapAssigns[sj]] = [bootstrapAssigns[sj], bootstrapAssigns[si]];
  }
  for (const a of bootstrapAssigns) lines.push(a);
  const bp = randomName(2);

  const collatzDec = randomName(4);
  const cn = randomName(2);
  const ct = randomName(2);
  const ci = randomName(2);
  const ck = randomName(2);
  lines.push(`local function ${collatzDec}(${bp}) local ${cn}=${collatzSeed};local ${ct}={};for ${ci}=1,#${bp} do local ${ck}=${bBA}(${cn},0xFF);${ct}[${ci}]=${bSC}(${bBX}(${bp}[${ci}],${ck}));if ${cn}%2==0 then ${cn}=${bBR}(${cn},1) else ${cn}=${bBA}(${cn}*3+1,0x7FFFFFFF) end;if ${cn}<=1 then ${cn}=${bBX}(${collatzSeed},${ci}) end end;return ${bTC}(${ct}) end`);

  const resolverStyle = Math.floor(rng() * 3);
  const encCode1 = `{${collatzEncodeString("return getgenv()", collatzSeed).join(",")}}`;
  const encCode2 = `{${collatzEncodeString("return getfenv(0)", collatzSeed).join(",")}}`;
  const tmpF = randomName(3);
  const tmpR = randomName(3);
  const tblEsc = luaEsc("table");
  if (resolverStyle === 0) {
    lines.push(`local ${genv}=_G`);
    lines.push(`do local ${tmpF},${tmpR}=${bPC}(function() local _f=${bLS}(${collatzDec}(${encCode1}));if _f then return _f() end end);if ${tmpF} and ${bTY}(${tmpR})==${tblEsc} then ${genv}=${tmpR} end end`);
    lines.push(`do local ${tmpF},${tmpR}=${bPC}(function() local _f=${bLS}(${collatzDec}(${encCode2}));if _f then return _f() end end);if ${tmpF} and ${bTY}(${tmpR})==${tblEsc} then ${genv}=${tmpR} end end`);
  } else if (resolverStyle === 1) {
    const tmpG = randomName(3);
    lines.push(`local ${tmpG}=nil`);
    lines.push(`do local ${tmpF},${tmpR}=${bPC}(function() return ${bLS}(${collatzDec}(${encCode1}))() end);if ${tmpF} and ${bTY}(${tmpR})==${tblEsc} then ${tmpG}=${tmpR} end end`);
    lines.push(`if not ${tmpG} then local ${tmpF},${tmpR}=${bPC}(function() return ${bLS}(${collatzDec}(${encCode2}))() end);if ${tmpF} and ${bTY}(${tmpR})==${tblEsc} then ${tmpG}=${tmpR} end end`);
    lines.push(`local ${genv}=${tmpG} or _G`);
  } else {
    const fnName = randomName(4);
    lines.push(`local function ${fnName}() local ${tmpR};local _f=${bLS}(${collatzDec}(${encCode1}));if _f then local _o,_r=${bPC}(_f);if _o and ${bTY}(_r)==${tblEsc} then return _r end end;_f=${bLS}(${collatzDec}(${encCode2}));if _f then local _o,_r=${bPC}(_f);if _o and ${bTY}(_r)==${tblEsc} then return _r end end;return _G end`);
    lines.push(`local ${genv}=${fnName}()`);
  }

  const mtStyle = Math.floor(rng() * 3);
  const fbP = randomName(2);
  const fbK = randomName(2);
  const okV = randomName(2);
  const valV = randomName(2);
  const idxEsc = luaEsc("__index");
  if (mtStyle === 0) {
    lines.push(`local ${env}=${bSM}({},{[${idxEsc}]=function(${fbP},${fbK}) local ${okV},${valV}=${bPC}(function() return ${genv}[${fbK}] end);if ${okV} then return ${valV} end;return nil end})`);
  } else if (mtStyle === 1) {
    const mtVar = randomName(4);
    lines.push(`local ${mtVar}={[${idxEsc}]=function(${fbP},${fbK}) local ${okV},${valV}=${bPC}(function() return ${genv}[${fbK}] end);return ${okV} and ${valV} or nil end}`);
    lines.push(`local ${env}=${bSM}({},${mtVar})`);
  } else {
    lines.push(`local ${env}=${bSM}({},{[${idxEsc}]=function(${fbP},${fbK}) local ${valV}=${bRG}(${genv},${fbK});if ${valV}~=nil then return ${valV} end;local ${okV};${okV},${valV}=${bPC}(function() return ${genv}[${fbK}] end);return ${okV} and ${valV} or nil end})`);
  }

  const allGlobals = includeExecutor ? [...CORE_GLOBALS, ...EXECUTOR_GLOBALS] : [...CORE_GLOBALS];
  for (let si = allGlobals.length - 1; si > 0; si--) {
    const sj = Math.floor(rng() * (si + 1));
    [allGlobals[si], allGlobals[sj]] = [allGlobals[sj], allGlobals[si]];
  }
  const dk = n.dk;
  const encodedNames = allGlobals.map(g => `{${collatzEncodeString(g, collatzSeed).join(",")}}`);
  lines.push(`local ${dk}={${encodedNames.join(",")}}`);

  const iVar = n.iVar;
  const sVar = n.sVar;
  lines.push(`for ${iVar}=1,#${dk} do local ${sVar}=${collatzDec}(${dk}[${iVar}])`);
  lines.push(`local ${okV},${valV}=${bPC}(function() return ${genv}[${sVar}] end);if ${okV} then ${bRS}(${env},${sVar},${valV}) end end`);

  const encLookup = (s: string) => `${collatzDec}({${collatzEncodeString(s, collatzSeed).join(",")}})`;
  lines.push(`if not ${bRG}(${env},${encLookup("unpack")}) then local _t=${bRG}(${env},${encLookup("table")});if _t then ${bRS}(${env},${encLookup("unpack")},_t[${encLookup("unpack")}]) end end`);
  lines.push(`if not ${bRG}(${env},${encLookup("loadstring")}) then ${bRS}(${env},${encLookup("loadstring")},${bRG}(${env},${encLookup("load")})) end`);

  if (level === "max") {
    const dbV = randomName(3);
    const dbEnvV = randomName(3);
    const dangerousFns = ["getupvalue", "setupvalue", "getlocal", "setlocal", "sethook", "getinfo"];

    for (let si = dangerousFns.length - 1; si > 0; si--) {
      const sj = Math.floor(rng() * (si + 1));
      [dangerousFns[si], dangerousFns[sj]] = [dangerousFns[sj], dangerousFns[si]];
    }

    lines.push(`do local ${dbV}=${bRG}(${genv},${encLookup("debug")})`);
    lines.push(`if ${bTY}(${dbV})==${tblEsc} then`);
    for (const fn of dangerousFns) {
      lines.push(`${dbV}[${encLookup(fn)}]=${fn === "getinfo" ? "function() return {} end" : "nil"}`);
    }
    lines.push(`end`);

    lines.push(`local ${dbEnvV}=${bRG}(${env},${encLookup("debug")})`);
    lines.push(`if ${bTY}(${dbEnvV})==${tblEsc} then`);
    for (const fn of dangerousFns) {
      lines.push(`${dbEnvV}[${encLookup(fn)}]=${fn === "getinfo" ? "function() return {} end" : "nil"}`);
    }
    lines.push(`end end`);
  }

  return lines.join("\n") + "\n";
}

interface NameMap {
  run: string;
  env: string;
  genv: string;
  dk: string;
  iVar: string;
  sVar: string;
  K: string;
  code: string;
  protos: string;
  stack: string;
  stackTop: string;
  locals: string;
  localBoxes: string;
  ip: string;
  upvalues: string;
  varargs: string;
  varargCount: string;
  callBases: string;
  callBaseTop: string;
  handlers: string;
  doReturn: string;
  retFromStack: string;
  retBase: string;
  retTop: string;
  retN: string;
  retPack: string;
  tailFn: string;
  tailArgs: string;
  tailN: string;
  getLocal: string;
  setLocal: string;
  boxLocal: string;
  push: string;
  pop: string;
  top: string;
  getMM: string;
  arithMM: string;
  initLocals: string;
  resolveK: string;
  ctxBit: string;
  jumpKey: string;
}

function createNames(level: VMGenLevel): NameMap {
  if (level === "debug") {
    return {
      run: "_run", env: "_env", genv: "_genv", dk: "_dk",
      iVar: "_i", sVar: "_s",
      K: "K", code: "code", protos: "protos",
      stack: "stack", stackTop: "stackTop",
      locals: "locals", localBoxes: "localBoxes",
      ip: "ip", upvalues: "upvalues",
      varargs: "varargs", varargCount: "varargCount",
      callBases: "callBases", callBaseTop: "callBaseTop",
      handlers: "handlers",
      doReturn: "_doReturn", retFromStack: "_retFromStack",
      retBase: "_retBase", retTop: "_retTop", retN: "_retN",
      retPack: "_retPack",
      tailFn: "_tailFn", tailArgs: "_tailArgs", tailN: "_tailN",
      getLocal: "getLocal", setLocal: "setLocal", boxLocal: "boxLocal",
      push: "push", pop: "pop", top: "top",
      getMM: "getMM", arithMM: "arithMM",
      initLocals: "initLocals",
      resolveK: "resolveK",
      ctxBit: "ctxBit",
      jumpKey: "jumpKey",
    };
  }
  return {
    run: randomName(5), env: randomName(4), genv: randomName(4), dk: randomName(4),
    iVar: randomName(3), sVar: randomName(3),
    K: randomName(3), code: randomName(4), protos: randomName(4),
    stack: randomName(4), stackTop: randomName(4),
    locals: randomName(4), localBoxes: randomName(5),
    ip: randomName(3), upvalues: randomName(5),
    varargs: randomName(4), varargCount: randomName(5),
    callBases: randomName(5), callBaseTop: randomName(5),
    handlers: randomName(4),
    doReturn: randomName(4), retFromStack: randomName(5),
    retBase: randomName(4), retTop: randomName(4), retN: randomName(3),
    retPack: randomName(4),
    tailFn: randomName(4), tailArgs: randomName(5), tailN: randomName(3),
    getLocal: randomName(5), setLocal: randomName(5), boxLocal: randomName(5),
    push: randomName(3), pop: randomName(3), top: randomName(3),
    getMM: randomName(4), arithMM: randomName(5),
    initLocals: randomName(5),
    resolveK: randomName(5),
    ctxBit: randomName(3),
    jumpKey: randomName(4),
  };
}

function buildHandlerTemplates(n: NameMap, doNonLinearJumps: boolean = false, protoKeys: { pK: string; pC: string; pP: string; pU: string; pN: string } = { pK: "K", pC: "C", pP: "P", pU: "U", pN: "nParams" }): Record<number, string> {
  const h: Record<number, string> = {};
  const { pK, pC, pP, pU, pN } = protoKeys;
  const {
    K, code, ip, push, pop, top, stack, stackTop, env, protos,
    upvalues, varargs, varargCount, locals, localBoxes,
    callBases, callBaseTop, getLocal, setLocal, boxLocal,
    getMM, arithMM, doReturn, retFromStack, retBase, retTop,
    retN, retPack, tailFn, tailArgs, tailN, run, resolveK
  } = n;

  h[0] = `function() end`;

  h[1] = `function() ${push}(nil) end`;

  h[2] = `function() ${push}(true) end`;

  h[3] = `function() ${push}(false) end`;

  h[4] = `function() ${push}(${resolveK}(${code}[${ip}]+1));${ip}=${ip}+1 end`;

  h[5] = `function() ${push}(${getLocal}(${code}[${ip}]));${ip}=${ip}+1 end`;

  h[6] = `function() ${setLocal}(${code}[${ip}],${pop}());${ip}=${ip}+1 end`;

  h[7] = `function() ${push}(${env}[${resolveK}(${code}[${ip}]+1)]);${ip}=${ip}+1 end`;

  h[8] = `function() ${env}[${resolveK}(${code}[${ip}]+1)]=${pop}();${ip}=${ip}+1 end`;

  h[9] = `function() local b,a=${pop}(),${pop}();${push}(${arithMM}(a,b,function(x,y) return x+y end,"__add")) end`;
  h[10] = `function() local b,a=${pop}(),${pop}();${push}(${arithMM}(a,b,function(x,y) return x-y end,"__sub")) end`;
  h[11] = `function() local b,a=${pop}(),${pop}();${push}(${arithMM}(a,b,function(x,y) return x*y end,"__mul")) end`;
  h[12] = `function() local b,a=${pop}(),${pop}();${push}(${arithMM}(a,b,function(x,y) return x/y end,"__div")) end`;
  h[13] = `function() local b,a=${pop}(),${pop}();${push}(${arithMM}(a,b,function(x,y) return x%y end,"__mod")) end`;
  h[14] = `function() local b,a=${pop}(),${pop}();${push}(${arithMM}(a,b,function(x,y) return x^y end,"__pow")) end`;

  h[15] = `function() local b,a=${pop}(),${pop}();local ok,r=pcall(function() return a..b end);if ok then ${push}(r) else ${push}(tostring(a)..tostring(b)) end end`;

  h[16] = `function() local b,a=${pop}(),${pop}();${push}(a==b) end`;
  h[17] = `function() local b,a=${pop}(),${pop}();${push}(a~=b) end`;
  h[18] = `function() local b,a=${pop}(),${pop}();${push}(a<b) end`;
  h[19] = `function() local b,a=${pop}(),${pop}();${push}(a<=b) end`;
  h[20] = `function() local b,a=${pop}(),${pop}();${push}(a>b) end`;
  h[21] = `function() local b,a=${pop}(),${pop}();${push}(a>=b) end`;

  h[22] = `function() local b,a=${pop}(),${pop}();${push}(a and b) end`;
  h[23] = `function() local b,a=${pop}(),${pop}();${push}(a or b) end`;

  h[24] = `function() ${push}(not ${pop}()) end`;

  h[25] = `function() ${push}(-${pop}()) end`;

  h[26] = `function() ${push}(#${pop}()) end`;

  h[27] = `function() ${push}({}) end`;

  h[28] = `function() local k,t=${pop}(),${pop}();${push}(t[k]) end`;

  h[29] = `function() local v,k,t=${pop}(),${pop}(),${pop}();t[k]=v end`;

  h[30] = `function() local n=${code}[${ip}];${ip}=${ip}+1;local args={};for i=1,n do args[n-i+1]=${pop}() end;local f=${pop}();if type(f)~="function" then local mm=${getMM}(f,"__call");if mm then table.insert(args,1,f);n=n+1;f=mm else error("attempt to call a "..type(f).." value") end end;local r;if n==0 then r={f()} else r={f(table.unpack(args,1,n))} end;${push}(r[1]) end`;

  h[31] = `function() local n=${code}[${ip}];${ip}=${ip}+1;${doReturn}=true;if n==0 then ${retN}=0 elseif n>0 then if n>${stackTop} then n=${stackTop} end;${retN}=n;${retFromStack}=true;${retTop}=${stackTop};${retBase}=${stackTop}-n else ${retN}=${stackTop};${retFromStack}=true;${retTop}=${stackTop};${retBase}=0 end end`;

  h[32] = doNonLinearJumps
    ? `function() ${ip}=bit32.bxor(${code}[${ip}],${n.jumpKey})+1 end`
    : `function() ${ip}=${code}[${ip}]+1 end`;

  h[33] = doNonLinearJumps
    ? `function() local target=bit32.bxor(${code}[${ip}],${n.jumpKey});${ip}=${ip}+1;if not ${pop}() then ${ip}=target+1 end end`
    : `function() local target=${code}[${ip}];${ip}=${ip}+1;if not ${pop}() then ${ip}=target+1 end end`;

  h[34] = `function() local n=${code}[${ip}];${ip}=${ip}+1;for _=1,n do ${pop}() end end`;

  h[35] = `function() local pi=${code}[${ip}]\n${ip}=${ip}+1\nlocal P=${protos}[pi]\nif P then\nlocal _r,Kp,Cp=${run},P.${pK} or ${K},P.${pC} or {}\nlocal nU={}\nif P.${pU} then for ui,ud in ipairs(P.${pU}) do local iL,idx=ud[1],ud[2]\nif iL==1 then nU[ui]=${boxLocal}(idx) else nU[ui]=${upvalues}[idx+1] end end end\nlocal nP=P.${pN} or 0\n${push}(function(...)\nlocal a={...}\nlocal ac=select("#",...)\nlocal L={}\nL.n=nP\nfor i=1,(ac<nP and ac or nP) do L[i-1]=a[i] end\nlocal va={}\nif ac>nP then for i=nP+1,ac do va[i-nP]=a[i] end end\nva.n=ac-nP\nreturn _r(Kp,Cp,${env},P.${pP} or {},L,nU,va)\nend)\nelse ${push}(nil) end end`;

  h[36] = `function() ${push}(${top}()) end`;

  h[37] = `function() local ui=${code}[${ip}];${ip}=${ip}+1;local box=${upvalues}[ui+1];${push}(box and box[1] or nil) end`;

  h[38] = `function() local ui=${code}[${ip}];${ip}=${ip}+1;local box=${upvalues}[ui+1];if box then box[1]=${pop}() else ${pop}() end end`;

  h[39] = `function() local na=${code}[${ip}];${ip}=${ip}+1;local nr=${code}[${ip}];${ip}=${ip}+1;local args={};for i=1,na do args[na-i+1]=${pop}() end;local f=${pop}();if type(f)~="function" then local mm=${getMM}(f,"__call");if mm then table.insert(args,1,f);na=na+1;f=mm else error("attempt to call a "..type(f).." value") end end;local r;if na==0 then r=table.pack(f()) else r=table.pack(f(table.unpack(args,1,na))) end;local rn=nr<0 and r.n or nr;for i=1,rn do ${push}(r[i]) end end`;

  h[40] = `function() local n=${code}[${ip}];${ip}=${ip}+1;if n<0 then for i=1,${varargCount} do ${push}(${varargs}[i]) end else for i=1,n do ${push}(${varargs}[i]) end end end`;

  h[41] = `function() local n=${code}[${ip}];${ip}=${ip}+1;local args={};for j=n,1,-1 do args[j]=${pop}() end;local f=${pop}();if type(f)~="function" then local mm=${getMM}(f,"__call");if mm then table.insert(args,1,f);n=n+1;f=mm end end;${tailFn}=f;${tailArgs}=args;${tailN}=n;${doReturn}=true end`;

  h[42] = doNonLinearJumps
    ? `function() local off=bit32.bxor(${code}[${ip}],${n.jumpKey});${ip}=${ip}+1;local step=${pop}();local limit=${pop}();local init=${pop}();${push}(init);${push}(limit);${push}(step);if step>=0 then if init>limit then ${ip}=off+1 end else if init<limit then ${ip}=off+1 end end end`
    : `function() local off=${code}[${ip}];${ip}=${ip}+1;local step=${pop}();local limit=${pop}();local init=${pop}();${push}(init);${push}(limit);${push}(step);if step>=0 then if init>limit then ${ip}=off+1 end else if init<limit then ${ip}=off+1 end end end`;

  h[43] = doNonLinearJumps
    ? `function() local off=bit32.bxor(${code}[${ip}],${n.jumpKey});${ip}=${ip}+1;local step=${stack}[${stackTop}];local i=${stack}[${stackTop}-2]+step;${stack}[${stackTop}-2]=i;local limit=${stack}[${stackTop}-1];if step>=0 then if i<=limit then ${ip}=off+1 end else if i>=limit then ${ip}=off+1 end end end`
    : `function() local off=${code}[${ip}];${ip}=${ip}+1;local step=${stack}[${stackTop}];local i=${stack}[${stackTop}-2]+step;${stack}[${stackTop}-2]=i;local limit=${stack}[${stackTop}-1];if step>=0 then if i<=limit then ${ip}=off+1 end else if i>=limit then ${ip}=off+1 end end end`;

  h[44] = `function() local n=${code}[${ip}];${ip}=${ip}+1;local parts={};for i=1,n do parts[n-i+1]=tostring(${pop}()) end;${push}(table.concat(parts)) end`;

  h[45] = `function() local n=${code}[${ip}];${ip}=${ip}+1;for _=1,n do ${push}(nil) end end`;

  h[46] = `function() ${callBaseTop}=${callBaseTop}+1;${callBases}[${callBaseTop}]=${stackTop} end`;

  h[47] = `function() local nr=${code}[${ip}];${ip}=${ip}+1;local base=${callBases}[${callBaseTop}];${callBaseTop}=${callBaseTop}-1;local f=${stack}[base+1];local na=${stackTop}-base-1;local args={};for i=1,na do args[i]=${stack}[base+1+i] end;${stackTop}=base;if type(f)~="function" then local mm=${getMM}(f,"__call");if mm then table.insert(args,1,f);na=na+1;f=mm else error("attempt to call a "..type(f).." value") end end;local r;if na==0 then r=table.pack(f()) else r=table.pack(f(table.unpack(args,1,na))) end;local rn=nr<0 and r.n or nr;for i=1,rn do ${push}(r[i]) end end`;

  h[48] = `function() local b,a=${pop}(),${pop}();${push}(${arithMM}(a,b,function(x,y) return math.floor(x/y) end,"__idiv")) end`;

  h[49] = `function() local slot=${code}[${ip}];${ip}=${ip}+1;local box=${localBoxes}[slot];if box then ${locals}[slot]=box[1];${localBoxes}[slot]=nil end end`;

  h[50] = `function() local startIdx=${code}[${ip}];${ip}=${ip}+1;local base=${callBases}[${callBaseTop}];${callBaseTop}=${callBaseTop}-1;local tbl=${stack}[base];local idx=startIdx;for i=base+1,${stackTop} do tbl[idx]=${stack}[i];idx=idx+1 end;${stackTop}=base;${stack}[${stackTop}]=tbl end`;

  h[51] = `function() local a=${stack}[${stackTop}];${stack}[${stackTop}]=${stack}[${stackTop}-1];${stack}[${stackTop}-1]=a end`;

  h[52] = `function() local nameIdx=${code}[${ip}];${ip}=${ip}+1;local methodName=${resolveK}(nameIdx+1);local obj=${pop}();local method=obj[methodName];${push}(obj);${push}(method);local b,a=${pop}(),${pop}();${push}(b);${push}(a) end`;

  h[53] = doNonLinearJumps
    ? `function() local nVars=${code}[${ip}];${ip}=${ip}+1;local target=bit32.bxor(${code}[${ip}],${n.jumpKey});${ip}=${ip}+1;local iter=${stack}[${stackTop}-2];local state=${stack}[${stackTop}-1];local ctl=${stack}[${stackTop}];local r={iter(state,ctl)};for i=1,nVars do ${push}(r[i]) end;if r[1]~=nil then ${stack}[${stackTop}-nVars]= r[1] else ${ip}=target+1 end end`
    : `function() local nVars=${code}[${ip}];${ip}=${ip}+1;local target=${code}[${ip}];${ip}=${ip}+1;local iter=${stack}[${stackTop}-2];local state=${stack}[${stackTop}-1];local ctl=${stack}[${stackTop}];local r={iter(state,ctl)};for i=1,nVars do ${push}(r[i]) end;if r[1]~=nil then ${stack}[${stackTop}-nVars]= r[1] else ${ip}=target+1 end end`;

  h[54] = `function() local n=${code}[${ip}];${ip}=${ip}+1;local args={};for i=1,n do args[n-i+1]=${pop}() end;local f=${pop}();local results;if n==0 then results=table.pack(pcall(f)) else results=table.pack(pcall(f,table.unpack(args,1,n))) end;local ok=results[1];${push}(ok);if ok then for i=2,results.n do ${push}(results[i]) end else ${push}(results[2]) end end`;

  h[55] = `function() local n=${code}[${ip}];${ip}=${ip}+1;local args={};for i=1,n do args[n-i+1]=${pop}() end;local handler=${pop}();local f=${pop}();local results;if n==0 then results=table.pack(xpcall(f,handler)) else results=table.pack(xpcall(f,handler,table.unpack(args,1,n))) end;local ok=results[1];${push}(ok);for i=2,results.n do ${push}(results[i]) end end`;

  h[56] = `function() local iS=${code}[${ip}];${ip}=${ip}+1;local sS=${code}[${ip}];${ip}=${ip}+1;local vS=${code}[${ip}];${ip}=${ip}+1;local it=${getLocal}(iS);if type(it)=="table" then local ok2,mt=pcall(getmetatable,it);if ok2 and type(mt)=="table" and mt.__iter then local fn=mt.__iter(it);${setLocal}(iS,fn) elseif ok2 and type(mt)=="table" and mt.__call then else ${setLocal}(iS,next);${setLocal}(sS,it);${setLocal}(vS,nil) end end end`;

  h[57] = `function() local a=${code}[${ip}];${ip}=${ip}+1;local b=${code}[${ip}];${ip}=${ip}+1;local c=${code}[${ip}];${ip}=${ip}+1;${setLocal}(c,${getLocal}(a)+${getLocal}(b)) end`;

  h[58] = `function() local a=${code}[${ip}];${ip}=${ip}+1;local b=${code}[${ip}];${ip}=${ip}+1;local c=${code}[${ip}];${ip}=${ip}+1;${setLocal}(c,${getLocal}(a)-${getLocal}(b)) end`;

  h[59] = `function() local a=${code}[${ip}];${ip}=${ip}+1;local b=${code}[${ip}];${ip}=${ip}+1;local c=${code}[${ip}];${ip}=${ip}+1;${setLocal}(c,${getLocal}(a)*${getLocal}(b)) end`;

  h[60] = `function() local k=${code}[${ip}];${ip}=${ip}+1;local s=${code}[${ip}];${ip}=${ip}+1;${setLocal}(s,${resolveK}(k+1)) end`;

  h[61] = `function() local a=${code}[${ip}];${ip}=${ip}+1;local b=${code}[${ip}];${ip}=${ip}+1;${setLocal}(b,${getLocal}(a)) end`;

  h[62] = `function() local a=${code}[${ip}];${ip}=${ip}+1;local k=${code}[${ip}];${ip}=${ip}+1;local c=${code}[${ip}];${ip}=${ip}+1;${setLocal}(c,${getLocal}(a)+${resolveK}(k+1)) end`;

  h[63] = `function() local a=${code}[${ip}];${ip}=${ip}+1;local b=${code}[${ip}];${ip}=${ip}+1;local c=${code}[${ip}];${ip}=${ip}+1;${setLocal}(c,${getLocal}(a)..${getLocal}(b)) end`;

  h[67] = `function() local _a=${code}[${ip}];${ip}=${ip}+1;if ${n.ctxBit}==0 then ${push}(${getLocal}(_a)) else ${push}(${resolveK}(_a+1)) end end`;

  h[64] = `function() local _=${stackTop} end`;

  h[65] = `function() local _a=${code}[${ip}];${ip}=${ip}+1;local _=${stack}[_a] or 0 end`;

  h[66] = `function() local _a=${code}[${ip}];${ip}=${ip}+1;local _b=${code}[${ip}];${ip}=${ip}+1;local _=bit32.bxor(_a,_b) end`;

  return h;
}

function generateFakeHandlers(n: NameMap, count: number, usedOps: Set<number>, hxkName: string = ""): string[] {
  const fakes: string[] = [];
  let nextFake = 64;
  for (let i = 0; i < count; i++) {
    while (usedOps.has(nextFake)) nextFake++;
    const op = nextFake++;
    const body = [
      `function() local _=${n.stackTop} or 0;_=_+1 end`,
      `function() local _={};_[1]=${n.ip};_=nil end`,
      `function() local _=bit32.bxor(${n.ip},0xFF) end`,
      `function() local _=${n.stackTop};_=_ and 0 or 1 end`,
      `function() local _=math.floor(${n.ip}/2) end`,
      `function() local _=type(${n.stack}) end`,
      `function() local _=tostring(${n.ip}) end`,
    ];
    const idx = hxkName ? `bit32.bxor(${op},${hxkName})` : `${op}`;
    fakes.push(`${n.handlers}[${idx}]=${body[i % body.length]}`);
  }
  return fakes;
}

function generateJunkCode(vmNames?: { ip?: string; stackTop?: string; code?: string; stack?: string; handlers?: string; stateAcc?: string }): string[] {
  const result: string[] = [];
  const count = 2 + Math.floor(rng() * 3);
  const r1 = Math.floor(rng() * 500) + 1;
  const r2 = Math.floor(rng() * 500) + 1;

  const impossibleVal = 0xDEAD + Math.floor(rng() * 0xFFFF);

  for (let i = 0; i < count; i++) {
    const v = `_z${_nameCounter++}`;
    const v2 = `_z${_nameCounter++}`;

    if (vmNames && vmNames.ip && rng() > 0.2) {
      const { ip, stackTop, code, stack, handlers, stateAcc } = vmNames;
      const smartPick = Math.floor(rng() * 10);

      if (smartPick === 0 && code && ip) {

        result.push(`do local ${v}=${code}[${ip}] or 0;local ${v2}=bit32.bxor(${v},${toHexInt(r1)});${v2}=nil end`);
      } else if (smartPick === 1 && stackTop) {

        result.push(`if ${stackTop}<0 then local ${v}=${r1}+${r2};${stackTop}=${v} end`);
      } else if (smartPick === 2 && stack && stackTop) {

        result.push(`do local ${v}={};${v}[bit32.band(${stackTop},0x7)]=${r1};${v}=nil end`);
      } else if (smartPick === 3 && handlers) {

        result.push(`do local ${v}=${handlers}[${Math.floor(rng() * 200)}];if ${v} and false then ${v}() end end`);
      } else if (smartPick === 4 && stateAcc) {

        result.push(`if bit32.band(${stateAcc},0xFFFF)==${toHexInt(impossibleVal)} then local ${v}=0 end`);
      } else if (smartPick === 5 && ip) {

        result.push(`do local ${v}=bit32.lrotate(${ip},${3 + Math.floor(rng() * 10)});${v}=bit32.bxor(${v},${toHexInt(r1)});${v}=nil end`);
      } else if (smartPick === 6 && code && ip) {

        result.push(`do local ${v}=${code}[${ip}+${Math.floor(rng() * 3)}] or 0;local ${v2}=bit32.band(${v},0xFF) end`);
      } else if (smartPick === 7 && stackTop) {

        result.push(`do local ${v}=${stackTop};if ${v}>${toHexInt(0xFFFF)} then ${v}=0 end end`);
      } else if (smartPick === 8 && ip && stateAcc) {

        result.push(`do local ${v}=bit32.bxor(${ip},${stateAcc});${v}=bit32.lrotate(${v},7) end`);
      } else {

        result.push(`do local ${v};pcall(function() ${v}=bit32.band(${toHexInt(r1)},${toHexInt(r2)}) end) end`);
      }
    } else {

      const pick = Math.floor(rng() * 6);
      if (pick === 0) result.push(`local ${v}=bit32.bxor(${toHexInt(r1)},${toHexInt(r2)})`);
      else if (pick === 1) result.push(`do local ${v}={};${v}[${Math.floor(rng()*5)+1}]=bit32.band(${toHexInt(r1)},${toHexInt(r2)});${v}=nil end`);
      else if (pick === 2) result.push(`local ${v}=bit32.lrotate(${r1},${Math.floor(rng()*20)+1})`);
      else if (pick === 3) result.push(`do local ${v}=pcall(function() return ${r1}+${r2} end) end`);
      else if (pick === 4) result.push(`local ${v}=select(1,${r1},${r2})`);
      else result.push(`local ${v}=type(${r1})=="number" and ${r2} or ${r1}`);
    }
  }
  return result;
}

function computeCodeHash(code: number[]): number {
  let hash = 0;
  for (const v of code) {
    const uv = v >= 0 ? v : (v + 0x100000000);
    hash = (hash ^ uv) >>> 0;
    hash = ((hash << 7) | (hash >>> 25)) >>> 0;
  }
  return hash >>> 0;
}

function randomOpaqueTrue(vmNames?: { ip?: string; stackTop?: string; handlers?: string; stateAcc?: string; code?: string }): string {
  const staticPool = [
    `math.floor(math.pi)==3`,
    `type(type)=="function"`,
    `select("#",1,2)>0`,
    `bit32.band(0xFF,0xFF)==0xFF`,
    `type(pcall)=="function"`,
    `math.abs(-1)==1`,
    `#""==0`,
    `type("")=="string"`,
    `1+1==2`,
    `not not true`,
    `type(0)=="number"`,
    `bit32.bor(0,0)==0`,
    `tostring(1)=="1"`,
    `type(math)=="table"`,
    `math.max(0,1)==1`,
    `type(nil)=="nil"`,
  ];

  const dynamicPool: string[] = [];
  if (vmNames) {
    const { ip, stackTop, handlers, stateAcc, code } = vmNames;
    if (stateAcc) {

      dynamicPool.push(`bit32.bxor(${stateAcc},${stateAcc})==0`);

      dynamicPool.push(`bit32.band(${stateAcc},0)==0`);

      dynamicPool.push(`bit32.bor(${stateAcc},${stateAcc})==${stateAcc}`);
    }
    if (stackTop) {

      dynamicPool.push(`${stackTop}>=0`);

      dynamicPool.push(`type(${stackTop})=="number"`);
    }
    if (handlers) {

      dynamicPool.push(`type(${handlers})=="table"`);
    }
    if (ip) {

      dynamicPool.push(`${ip}>0`);

      dynamicPool.push(`${ip}==${ip}`);
    }
    if (code) {

      dynamicPool.push(`type(${code})=="table"`);
    }
  }

  const useDynamic = dynamicPool.length > 0 && rng() > 0.4;
  const base = useDynamic
    ? dynamicPool[Math.floor(rng() * dynamicPool.length)]
    : staticPool[Math.floor(rng() * staticPool.length)];

  const r = Math.floor(rng() * 200) + 1;
  const wrapStyle = Math.floor(rng() * 4);
  if (wrapStyle === 0) return base;
  if (wrapStyle === 1) return `(${r}+${r}==${r*2} and ${base})`;
  if (wrapStyle === 2) return `(${base} and ${r}==${r})`;

  const extra = staticPool[Math.floor(rng() * staticPool.length)];
  return `(${base} and ${extra})`;
}

function generateAntiDebugChecks(): string[] {
  const checks: string[] = [];
  const flag = randomName(3);
  checks.push(`local ${flag}=false`);

  const allChecks: string[] = [];
  const r1 = Math.floor(rng() * 200) + 50;
  const t1 = randomName(3);
  allChecks.push(`if type(pcall)~="function" then ${flag}=true end`);
  allChecks.push(`if type(select)~="function" then ${flag}=true end`);
  allChecks.push(`if type(type)~="function" then ${flag}=true end`);
  allChecks.push(`if select("#",pcall(function() end))~=2 then ${flag}=true end`);
  allChecks.push(`if type(tostring)~="function" then ${flag}=true end`);
  allChecks.push(`if type(rawget)~="function" then ${flag}=true end`);
  allChecks.push(`do local ${t1}=(type(tick)=="function" and tick()) or 0;local _=0;for _i=1,${r1} do _=_+1 end;if ${t1}>0 and ((type(tick)=="function" and tick()) or 0)-${t1}>0.1 then ${flag}=true end end`);

  for (let si = allChecks.length - 1; si > 0; si--) {
    const sj = Math.floor(rng() * (si + 1));
    [allChecks[si], allChecks[sj]] = [allChecks[sj], allChecks[si]];
  }
  const pickCount = 2 + Math.floor(rng() * 2);
  for (let ci = 0; ci < pickCount && ci < allChecks.length; ci++) {
    checks.push(allChecks[ci]);
  }
  return checks;
}

function minify(code: string): string {

  code = code.replace(/--[^\n]*/g, "");

  code = code.replace(/\n+/g, " ");

  code = code.replace(/ {2,}/g, " ");
  return code.trim();
}

function buildVMFunction(
  n: NameMap,
  opcodeEncode: number[],
  level: VMGenLevel,
  encodeStrings: boolean,
  xorKey: number = 0,
  xorStep: number = 0,
  codeXorKey: number = 0,
  codeHash: number = 0,
  lazyBaseKey: number = 0,
  lazyKeyPrime: number = 0,
  ctxInit: number = 0,
  ctxPrime: number = 0,
  jumpKeyVal: number = 0,
  protoKeys: { pK: string; pC: string; pP: string; pU: string; pN: string } = { pK: "K", pC: "C", pP: "P", pU: "U", pN: "nParams" },
  cipherSeeds?: [number, number, number],
  doMutation: boolean = false,
  doPooling: boolean = false,
  poolsVarName: string = "",
): string {
  const doLazyDecode = lazyBaseKey !== 0;
  const doStringPools = poolsVarName !== "";
  const doContextOps = ctxInit !== 0;
  const doJumpEnc = jumpKeyVal !== 0;
  const doMultiLayer = !!cipherSeeds;
  const handlers = buildHandlerTemplates(n, doJumpEnc, protoKeys);
  const lines: string[] = [];

  if (doStringPools) {
    lines.push(`local ${poolsVarName}`);
  }

  const poolStk = doPooling ? randomName(3) : "";
  const poolLoc = doPooling ? randomName(3) : "";
  const poolCb = doPooling ? randomName(3) : "";
  const poolMax = 16;
  if (doPooling) {
    lines.push(`local ${poolStk}={}`);
    lines.push(`local ${poolLoc}={}`);
    lines.push(`local ${poolCb}={}`);
  }

  lines.push(`local function ${n.run}(${n.K},${n.code},${n.env},${n.protos},${n.initLocals},${n.upvalues},${n.varargs})`);
  lines.push(`${n.protos}=${n.protos} or {}`);
  lines.push(`${n.upvalues}=${n.upvalues} or {}`);
  lines.push(`${n.varargs}=${n.varargs} or {}`);
  lines.push(`local ${n.varargCount}=${n.varargs}.n or #${n.varargs}`);

  if (doLazyDecode) {

    const bk = toHexInt(lazyBaseKey >>> 0);
    const kp = toHexInt(lazyKeyPrime >>> 0);

    if (doMutation) {

      const decFn = randomName(4);
      lines.push(`local ${decFn}=function(_e,_dk,_s) if _s==0 then return bit32.bxor(_e,_dk) elseif _s==1 then return (_e-_dk+256)%256 elseif _s==2 then return bit32.bxor(_e,bit32.band(bit32.bor(bit32.lshift(_dk,3),bit32.rshift(_dk,5)),0xFF)) else return (_e-bit32.bxor(_dk,0xAA)+256)%256 end end`);

      lines.push(`local function ${n.resolveK}(_idx)`);
      lines.push(`local _v=${n.K}[_idx]`);
      lines.push(`if type(_v)~="table" then return _v end`);
      lines.push(`if #_v==0 then return "" end`);

      lines.push(`if _v[1]==-999 then local _r=bit32.bxor(_v[2],_v[3]);${n.K}[_idx]=_r;return _r end`);

      lines.push(`local _k=bit32.bxor(${bk},_idx*${kp})`);
      lines.push(`local _st=bit32.band(bit32.rshift(_k,16),3)`);

      if (doStringPools) {
        lines.push(`if _v[1]==-998 then local _pl=${poolsVarName}[_v[2]];local _off=_v[3];local _ol=_v[4];local _t={}`);
        lines.push(`for _j=1,_ol do local _dk=bit32.band(_k,0xFF);local _b=${decFn}(_pl[_off+_j-1],_dk,_st);_t[_j]=_b;_k=bit32.lrotate(bit32.bxor(_k,_b),7) end`);
        lines.push(`return string.char(table.unpack(_t)) end`);
      }

      lines.push(`if _v[1]<0 then`);
      lines.push(`local _nF=-_v[1];local _fS=_v[2];local _oL=_v[4];local _hd=4+_nF;local _t={};local _ti=0`);
      lines.push(`for _fi=1,_nF do local _sp=_v[4+_fi];local _off=_hd+(_sp-1)*_fS`);
      lines.push(`for _bi=1,_fS do _ti=_ti+1;local _dk=bit32.band(_k,0xFF);local _b=${decFn}(_v[_off+_bi],_dk,_st);if _ti<=_oL then _t[_ti]=_b end;_k=bit32.lrotate(bit32.bxor(_k,_b),7) end end`);
      lines.push(`return string.char(table.unpack(_t,1,_oL))`);
      lines.push(`end`);

      lines.push(`local _t={}`);
      lines.push(`for _j=1,#_v do local _dk=bit32.band(_k,0xFF);local _b=${decFn}(_v[_j],_dk,_st);_t[_j]=_b;_k=bit32.lrotate(bit32.bxor(_k,_b),7) end`);
      lines.push(`return string.char(table.unpack(_t))`);
      lines.push(`end`);
    } else {

      lines.push(`local function ${n.resolveK}(_idx)`);
      lines.push(`local _v=${n.K}[_idx]`);
      lines.push(`if type(_v)~="table" then return _v end`);
      lines.push(`if #_v==0 then return "" end`);

      lines.push(`if _v[1]==-999 then local _r=bit32.bxor(_v[2],_v[3]);${n.K}[_idx]=_r;return _r end`);
      lines.push(`local _k=bit32.bxor(${bk},_idx*${kp})`);

      if (doStringPools) {
        lines.push(`if _v[1]==-998 then local _pl=${poolsVarName}[_v[2]];local _off=_v[3];local _ol=_v[4];local _t={}`);
        lines.push(`for _j=1,_ol do local _dk=bit32.band(_k,0xFF);local _b=bit32.bxor(_pl[_off+_j-1],_dk);_t[_j]=_b;_k=bit32.lrotate(bit32.bxor(_k,_b),7) end`);
        lines.push(`return string.char(table.unpack(_t)) end`);
      }

      lines.push(`if _v[1]<0 then`);
      lines.push(`local _nF=-_v[1];local _fS=_v[2];local _oL=_v[4];local _hd=4+_nF;local _t={};local _ti=0`);
      lines.push(`for _fi=1,_nF do local _sp=_v[4+_fi];local _off=_hd+(_sp-1)*_fS`);
      lines.push(`for _bi=1,_fS do _ti=_ti+1;local _dk=bit32.band(_k,0xFF);local _b=bit32.bxor(_v[_off+_bi],_dk);if _ti<=_oL then _t[_ti]=_b end;_k=bit32.lrotate(bit32.bxor(_k,_b),7) end end`);
      lines.push(`return string.char(table.unpack(_t,1,_oL))`);
      lines.push(`end`);

      lines.push(`local _t={}`);
      lines.push(`for _j=1,#_v do local _dk=bit32.band(_k,0xFF);local _b=bit32.bxor(_v[_j],_dk);_t[_j]=_b;_k=bit32.lrotate(bit32.bxor(_k,_b),7) end`);
      lines.push(`return string.char(table.unpack(_t))`);
      lines.push(`end`);
    }

  } else {

    lines.push(`local function ${n.resolveK}(_idx) return ${n.K}[_idx] end`);

    if (encodeStrings) {

      const keyExpr = `bit32.band(${xorKey}+(_j-1)*${xorStep}+(_i-1),0xFF)`;
      const ce = `bit32.bxor(_v[_j],${keyExpr})`;

      const keyExprF = `bit32.band(${xorKey}+_p*${xorStep}+(_i-1),0xFF)`;
      const cef = `bit32.bxor(_v[_fi][_j],${keyExprF})`;

      const decBody = `if type(_v)=="table" then local _s="";if type(_v[1])=="table" then local _p=0;for _fi=1,#_v do for _j=1,#_v[_fi] do _s=_s..string.char(${cef});_p=_p+1 end end else for _j=1,#_v do _s=_s..string.char(${ce}) end end`;
      lines.push(`for _i,_v in ipairs(${n.K}) do ${decBody};${n.K}[_i]=_s end end`);

      const dpName = level === "debug" ? "_decProtos" : randomName(5);
      lines.push(`local function ${dpName}(ps) for _,p in ipairs(ps) do if p.K then for _i,_v in ipairs(p.K) do ${decBody};p.K[_i]=_s end end end;if p.P then ${dpName}(p.P) end end end`);
      lines.push(`${dpName}(${n.protos})`);
    }
  }

  if (doMultiLayer && cipherSeeds) {

    const _decFn = randomName(5);
    const s1 = toHexInt(cipherSeeds[0] >>> 0);
    const s2 = toHexInt(cipherSeeds[1] >>> 0);
    const s3 = toHexInt(cipherSeeds[2] >>> 0);
    lines.push(`local function ${_decFn}(_enc)`);

    lines.push(`local _b={};for _i=1,#_enc do _b[_i]=string.byte(_enc,_i) end;local _len=#_b`);

    lines.push(`local _pv=bit32.band(${s3},0xFF);for _i=1,_len do local _c=_b[_i];_b[_i]=bit32.bxor(_c,_pv);_pv=_c end`);

    lines.push(`local _ka=bit32.band(${s2},0xFF);local _kb=bit32.band(bit32.rshift(${s2},8),0xFF);for _i=1,_len do _b[_i]=(_b[_i]-_ka+256)%256;local _t=(_ka+_kb)%256;_ka=_kb;_kb=_t end`);

    lines.push(`local _cs=${s1};for _i=1,_len do _b[_i]=bit32.bxor(_b[_i],bit32.band(_cs,0xFF));if _cs%2==0 then _cs=bit32.rshift(_cs,1) else _cs=bit32.band(_cs*3+1,0x7FFFFFFF) end;if _cs<=1 then _cs=bit32.bor(bit32.bxor(${s1},_i),2) end end`);

    lines.push(`local _r={};local _p=1;while _p<=_len do local _v=_b[_p]`);
    lines.push(`if _v==255 then _r[#_r+1]=-1;_p=_p+1`);
    lines.push(`elseif _v<128 then _r[#_r+1]=_v;_p=_p+1`);
    lines.push(`elseif _v<192 then _r[#_r+1]=(_v-128)*256+_b[_p+1];_p=_p+2`);
    lines.push(`elseif _v<224 then _r[#_r+1]=(_v-192)*65536+_b[_p+1]*256+_b[_p+2];_p=_p+3`);
    lines.push(`else _r[#_r+1]=(_v-224)*16777216+_b[_p+1]*65536+_b[_p+2]*256+_b[_p+3];_p=_p+4 end end`);
    lines.push(`return _r end`);

    lines.push(`if type(${n.code})=="string" then ${n.code}=${_decFn}(${n.code}) end`);

    const _decProtos = randomName(5);
    lines.push(`local function ${_decProtos}(_ps) for _,_p in ipairs(_ps) do if type(_p.${protoKeys.pC})=="string" then _p.${protoKeys.pC}=${_decFn}(_p.${protoKeys.pC}) end;if _p.${protoKeys.pP} then ${_decProtos}(_p.${protoKeys.pP}) end end end`);
    lines.push(`${_decProtos}(${n.protos})`);
  } else if (codeXorKey) {

    lines.push(`if not ${n.code}[0] then for _i=1,#${n.code} do if ${n.code}[_i]>=0 then ${n.code}[_i]=bit32.bxor(${n.code}[_i],${codeXorKey}) end end;${n.code}[0]=true end`);
    const dcpName = level === "debug" ? "_decCode" : randomName(5);
    lines.push(`local function ${dcpName}(ps) for _,p in ipairs(ps) do if p.C and not p.C[0] then for _i=1,#p.C do if p.C[_i]>=0 then p.C[_i]=bit32.bxor(p.C[_i],${codeXorKey}) end end;p.C[0]=true end;if p.P then ${dcpName}(p.P) end end end`);
    lines.push(`${dcpName}(${n.protos})`);
  }

  if (codeHash && level === "max") {
    const hv = randomName(3);
    lines.push(`if not ${n.initLocals} then do local ${hv}=0;for _i=1,#${n.code} do local _v=${n.code}[_i];if _v<0 then _v=_v+0x100000000 end;${hv}=bit32.bxor(${hv},_v);${hv}=bit32.lrotate(${hv},7) end`);
    lines.push(`if ${hv}~=${codeHash} then for _k in pairs(${n.handlers}) do ${n.handlers}[_k]=nil end end end end`);
  }

  if (doPooling) {

    lines.push(`local ${n.stack}=table.remove(${poolStk}) or (table.create and table.create(64,nil) or {})`);
    lines.push(`local ${n.locals}=table.remove(${poolLoc}) or (table.create and table.create(32,nil) or {})`);
    lines.push(`local ${n.callBases}=table.remove(${poolCb}) or (table.create and table.create(8,nil) or {})`);
  } else {
    lines.push(`local ${n.stack}={}`);
    lines.push(`local ${n.locals}={}`);
    lines.push(`local ${n.callBases}={}`);
  }
  lines.push(`local ${n.stackTop}=0`);
  lines.push(`local ${n.localBoxes}={}`);
  lines.push(`local ${n.ip}=1`);
  lines.push(`local ${n.callBaseTop}=0`);
  lines.push(`local ${n.doReturn}=false`);
  lines.push(`local ${n.retFromStack}=false`);
  lines.push(`local ${n.retBase}=0`);
  lines.push(`local ${n.retTop}=0`);
  lines.push(`local ${n.retN}=0`);
  lines.push(`local ${n.retPack}=nil`);
  lines.push(`local ${n.tailFn}=nil`);
  lines.push(`local ${n.tailArgs}=nil`);
  lines.push(`local ${n.tailN}=0`);
  lines.push(`local ${n.ctxBit}=0`);
  if (doJumpEnc) {
    lines.push(`local ${n.jumpKey}=${toHexInt(jumpKeyVal)}`);
  }

  lines.push(`if ${n.initLocals} then for _k=0,(${n.initLocals}.n or 0)-1 do ${n.locals}[_k]=${n.initLocals}[_k] end end`);

  if (level === "max") {
    const incVariants = [
      `${n.stackTop}=${n.stackTop}-(-(1))`,
      `${n.stackTop}=${n.stackTop}+bit32.band(1,0xFF)`,
      `${n.stackTop}=${n.stackTop}+bit32.rshift(2,1)`,
      `${n.stackTop}=${n.stackTop}+(2-1)`,
    ];
    const decVariants = [
      `${n.stackTop}=${n.stackTop}+(-(1))`,
      `${n.stackTop}=${n.stackTop}-bit32.band(1,0xFF)`,
      `${n.stackTop}=${n.stackTop}-(2-1)`,
      `${n.stackTop}=${n.stackTop}+(-bit32.band(1,0xFF))`,
    ];
    const inc = incVariants[Math.floor(rng() * incVariants.length)];
    const dec = decVariants[Math.floor(rng() * decVariants.length)];
    lines.push(`local function ${n.push}(v) ${inc};${n.stack}[${n.stackTop}]=v end`);
    lines.push(`local function ${n.pop}() local v=${n.stack}[${n.stackTop}];${n.stack}[${n.stackTop}]=nil;${dec};return v end`);
  } else {
    lines.push(`local function ${n.push}(v) ${n.stackTop}=${n.stackTop}+1;${n.stack}[${n.stackTop}]=v end`);
    lines.push(`local function ${n.pop}() local v=${n.stack}[${n.stackTop}];${n.stack}[${n.stackTop}]=nil;${n.stackTop}=${n.stackTop}-1;return v end`);
  }
  lines.push(`local function ${n.top}() return ${n.stack}[${n.stackTop}] end`);

  lines.push(`local function ${n.getLocal}(slot) local box=${n.localBoxes}[slot];if box then return box[1] end;return ${n.locals}[slot] end`);
  lines.push(`local function ${n.setLocal}(slot,val) local box=${n.localBoxes}[slot];if box then box[1]=val else ${n.locals}[slot]=val end end`);
  lines.push(`local function ${n.boxLocal}(slot) if not ${n.localBoxes}[slot] then ${n.localBoxes}[slot]={${n.locals}[slot]} end;return ${n.localBoxes}[slot] end`);

  lines.push(`local function ${n.getMM}(obj,name) local ok,mt=pcall(getmetatable,obj);if ok and mt and type(mt)=="table" then return rawget(mt,name) end;return nil end`);
  lines.push(`local function ${n.arithMM}(a,b,op,name) if type(a)=="number" and type(b)=="number" then return op(a,b) end;local ok,r=pcall(op,a,b);if ok then return r end;local mm=${n.getMM}(a,name) or ${n.getMM}(b,name);if mm then return mm(a,b) end;return op(a,b) end`);

  lines.push(`local ${n.handlers}={}`);

  const handlerXorKey = level === "max" ? (1 + Math.floor(rng() * 0xFFFE)) : 0;
  const hxk = randomName(3);
  if (handlerXorKey) {
    lines.push(`local ${hxk}=${handlerXorKey}`);
  }

  const pushAliases: string[] = [n.push];
  const popAliases: string[] = [n.pop];
  if (level === "max") {
    for (let ai = 0; ai < 2; ai++) {
      const pa = randomName(3);
      const qa = randomName(3);
      pushAliases.push(pa);
      popAliases.push(qa);
      lines.push(`local ${pa}=${n.push}`);
      lines.push(`local ${qa}=${n.pop}`);
    }
  }

  const handlerSetter = randomName(4);
  if (level === "max") {
    if (handlerXorKey) {
      lines.push(`local function ${handlerSetter}(_k,_f) ${n.handlers}[bit32.bxor(_k,${hxk})]=_f end`);
    } else {
      lines.push(`local function ${handlerSetter}(_k,_f) ${n.handlers}[_k]=_f end`);
    }
  }

  const usedOps = new Set<number>();
  const handlerAssignments: string[] = [];

  const inlineBodies: Map<number, string> = new Map();
  for (let realOp = 0; realOp < 68; realOp++) {
    if (!handlers[realOp]) continue;
    const shuffledOp = opcodeEncode[realOp];
    usedOps.add(shuffledOp);
    let h = handlers[realOp];

    if (level === "max" && pushAliases.length > 1) {
      const pu = pushAliases[Math.floor(rng() * pushAliases.length)];
      const po = popAliases[Math.floor(rng() * popAliases.length)];
      if (pu !== n.push) h = h.split(n.push + '(').join(pu + '(');
      if (po !== n.pop) h = h.split(n.pop + '(').join(po + '(');
    }
    if (level === "max" && rng() > 0.3) {

      const dv = randomName(2);
      const noises = [
        `local ${dv}=${n.stackTop}`,
        `local ${dv}=${n.ip}`,
        `local ${dv}=bit32.band(${n.ip},0xFF)`,
        `local ${dv}=type(${n.stack})`,
        `local ${dv}=${n.code}[${n.ip}] or 0`,
      ];
      const noise = noises[Math.floor(rng() * noises.length)];
      h = h.replace('function()', `function() ${noise}\n`);
    }

    if (level === "max") {
      let body = h;

      const fnMatch = body.match(/^function\(\)\s*([\s\S]*)\s*end$/);
      if (fnMatch) {
        inlineBodies.set(shuffledOp, fnMatch[1].trim());
      }
    }

    if (level === "max") {
      const style = Math.floor(rng() * 4);
      const xIdx = handlerXorKey ? `bit32.bxor(${shuffledOp},${hxk})` : `${shuffledOp}`;
      if (style === 0) {

        handlerAssignments.push(`${n.handlers}[${xIdx}]=${h}`);
      } else if (style === 1) {

        handlerAssignments.push(`${handlerSetter}(${shuffledOp},${h})`);
      } else if (style === 2) {

        const tmpH = randomName(3);
        handlerAssignments.push(`do local ${tmpH}=${h};${n.handlers}[${xIdx}]=${tmpH} end`);
      } else {

        const tmpH = randomName(3);
        const jv = randomName(2);
        handlerAssignments.push(`do local ${jv}=${Math.floor(rng()*9999)};local ${tmpH}=${h};${n.handlers}[${xIdx}]=${tmpH} end`);
      }
    } else {
      handlerAssignments.push(`${n.handlers}[${shuffledOp}]=${h}`);
    }
  }

  const detFlag = level === "max" ? randomName(4) : "";
  const sigTable = level === "max" ? randomName(4) : "";
  const punishDelay = level === "max" ? randomName(3) : "";

  if (level === "max") {

    lines.push(...generateAntiDebugChecks());

    const groupCount = 3 + Math.floor(rng() * 3);
    const shuffledAssignments = [...handlerAssignments].sort(() => rng() - 0.5);
    const groupSize = Math.ceil(shuffledAssignments.length / groupCount);
    for (let g = 0; g < groupCount; g++) {
      const start = g * groupSize;
      const end = Math.min(start + groupSize, shuffledAssignments.length);
      if (start >= shuffledAssignments.length) break;

      lines.push(`if ${randomOpaqueTrue({ ip: n.ip, stackTop: n.stackTop, handlers: n.handlers, code: n.code })} then`);
      lines.push(`;(function()`);

      lines.push(...generateJunkCode({ ip: n.ip, stackTop: n.stackTop, code: n.code, stack: n.stack, handlers: n.handlers }));
      for (let i = start; i < end; i++) {
        lines.push(shuffledAssignments[i]);
      }
      lines.push(`end)()`);
      lines.push(`end`);

      if (g < groupCount - 1) {
        lines.push(...generateJunkCode({ ip: n.ip, stackTop: n.stackTop, code: n.code, stack: n.stack, handlers: n.handlers }));
      }
    }

    const fakeCount = 15 + Math.floor(rng() * 11);
    lines.push(...generateFakeHandlers(n, fakeCount, usedOps, handlerXorKey ? hxk : ""));

    if (handlerXorKey) {
      lines.push(`for _ak=0,127 do local _xk=bit32.bxor(_ak,${hxk});if ${n.handlers}[_xk] then ${n.handlers}[_xk+128]=${n.handlers}[_xk] end end`);
    } else {
      lines.push(`for _ak=0,67 do if ${n.handlers}[_ak] then ${n.handlers}[_ak+128]=${n.handlers}[_ak] end end`);
    }

    lines.push(`local ${detFlag}=0`);
    lines.push(`local ${punishDelay}=0`);

    const builtinNames = ["pcall","type","rawget","rawset","tostring","tonumber","select","error","setmetatable","getmetatable","rawequal","next"];
    for (let bi = builtinNames.length - 1; bi > 0; bi--) {
      const bj = Math.floor(rng() * (bi + 1));
      [builtinNames[bi], builtinNames[bj]] = [builtinNames[bj], builtinNames[bi]];
    }
    lines.push(`local ${sigTable}={}`);
    for (const b of builtinNames) {
      const sv = randomName(2);
      lines.push(`do local ${sv}=${b};if type(${sv})=="function" then ${sigTable}[${sv}]=tostring(${sv}) end end`);
    }

    const mtV = randomName(2);
    lines.push(`do local ${mtV}=getmetatable("");if not ${mtV} or type(${mtV})~="table" then ${detFlag}=${detFlag}+1 end end`);
    lines.push(`if getmetatable(0)~=nil then ${detFlag}=${detFlag}+1 end`);

    lines.push(`if select("#",pcall(function() return 1 end))~=2 then ${detFlag}=${detFlag}+1 end`);

    const slV = randomName(2);
    lines.push(`do local ${slV}=getmetatable("");if ${slV} then local _ok,_r=pcall(function() return ("\\0")[("byte")]("\\0",1) end);if not _ok or _r~=0 then ${detFlag}=${detFlag}+1 end end end`);

    const sbOk = randomName(2);
    const sbTy = randomName(2);
    lines.push(`do local ${sbOk},_g=pcall(function() return game end)`);
    lines.push(`if ${sbOk} and _g then`);
    lines.push(`local ${sbTy}=(type(typeof)=="function" and typeof(_g)) or ""`);
    lines.push(`if ${sbTy}~="" and ${sbTy}~="Instance" then ${detFlag}=${detFlag}+1 end`);
    const wpOk = randomName(2);
    lines.push(`local ${wpOk},_wp=pcall(function() return workspace.Parent end)`);
    lines.push(`if ${wpOk} and _wp~=_g then ${detFlag}=${detFlag}+1 end`);
    lines.push(`end end`);

    const tWork = 200 + Math.floor(rng() * 600);
    const tV = randomName(2);
    lines.push(`do local ${tV}=(type(tick)=="function" and tick()) or 0`);
    lines.push(`local _s=0;for _i=1,${tWork} do _s=bit32.bxor(_s,_i) end`);
    lines.push(`local _t2=(type(tick)=="function" and tick()) or 0`);
    lines.push(`if ${tV}>0 and _t2-${tV}>0.05 then ${detFlag}=${detFlag}+1 end end`);

    lines.push(`if ${detFlag}>1 then for _hk,_ in pairs(${n.handlers}) do ${n.handlers}[_hk]=function() end end end`);
  } else {

    for (const assignment of handlerAssignments) {
      lines.push(assignment);
    }
  }

  if (level === "max") {

    const stVar = randomName(3);
    const cycleVar = randomName(4);
    const origVar = randomName(4);
    const dv1 = randomName(2);
    const dv2 = randomName(2);
    const dispMode = randomName(3);
    const S_RUN = 10 + Math.floor(rng() * 90);
    const S_DEAD1 = 200 + Math.floor(rng() * 90);
    const S_DEAD2 = 400 + Math.floor(rng() * 90);
    const S_DEAD3 = 600 + Math.floor(rng() * 90);

    const switchMask = [0x3F, 0x7F, 0xFF, 0x1FF][Math.floor(rng() * 4)];
    const switchThresh = Math.floor(rng() * 4);

    const opA = randomName(2);
    const hA = randomName(2);
    const opB = randomName(3);
    const hB = randomName(3);
    const lastOp = randomName(3);

    const stateAcc = randomName(4);
    const stateInit = Math.floor(rng() * 0xFFFFFFFF) >>> 0;
    const rotAmt = 3 + Math.floor(rng() * 10);
    const decoyVal = Math.floor(rng() * 0xFFFF) >>> 0;

    const ipMask = randomName(4);
    const ipMaskInit = (Math.floor(rng() * 0xFFFFFFFF) + 1) >>> 0;
    const ipRotAmt = 3 + Math.floor(rng() * 8);

    lines.push(`local ${stVar}=${S_RUN}`);
    lines.push(`local ${cycleVar}=0`);
    lines.push(`local ${dv1},${dv2}=0,0`);
    lines.push(`local ${dispMode}=0`);
    lines.push(`local ${stateAcc}=${toHexInt(stateInit)}`);
    lines.push(`local ${lastOp}=0`);
    lines.push(`local ${ipMask}=${toHexInt(ipMaskInit)}`);
    lines.push(`local ${origVar}={}`);
    lines.push(`for _k,_v in pairs(${n.handlers}) do ${origVar}[_k]=_v end`);

    if (handlerXorKey) {
      const ahFlag = randomName(2);
      lines.push(`local ${ahFlag}=0`);
    }

    lines.push(`while ${stVar}~=${S_DEAD3} do`);

    lines.push(`if ${stVar}==${S_DEAD1} then ${dv1}=${n.stackTop};${stVar}=${S_DEAD2}`);

    lines.push(`elseif ${stVar}==${S_DEAD2} then ${dv2}=${n.ip};${stVar}=${S_DEAD1}`);

    lines.push(`else`);

    lines.push(`${n.ip}=bit32.bxor(${n.ip},${ipMask})`);

    lines.push(`while true do`);

    lines.push(`${n.ip}=bit32.bxor(${n.ip},${ipMask})`);
    lines.push(`if ${n.doReturn} or ${n.ip}>#${n.code} then break end`);

    if (doContextOps) {
      lines.push(`${n.ctxBit}=bit32.band(bit32.rshift(bit32.bxor(${toHexInt(ctxInit)},${n.ip}*${toHexInt(ctxPrime)}),16),1)`);
    }

    lines.push(`if ${dispMode}==0 then`);
    lines.push(`local ${opA}=${n.code}[${n.ip}]`);
    lines.push(`${n.ip}=${n.ip}+1`);
    lines.push(`${lastOp}=${opA}`);

    const inlineOps = Array.from(inlineBodies.keys());

    for (let si = inlineOps.length - 1; si > 0; si--) {
      const sj = Math.floor(rng() * (si + 1));
      [inlineOps[si], inlineOps[sj]] = [inlineOps[sj], inlineOps[si]];
    }
    for (let bi = 0; bi < inlineOps.length; bi++) {
      const sOp = inlineOps[bi];
      const body = inlineBodies.get(sOp)!;
      if (bi === 0) {
        lines.push(`if ${opA}==${sOp} then`);
      } else {
        lines.push(`elseif ${opA}==${sOp} then`);
      }
      lines.push(`do ${body} end`);
    }

    lines.push(`else`);
    lines.push(handlerXorKey ? `local ${hA}=${n.handlers}[bit32.bxor(${opA},${hxk})]` : `local ${hA}=${n.handlers}[${opA}]`);
    lines.push(`if ${hA} then ${hA}() end`);
    lines.push(`end`);

    lines.push(`else`);
    lines.push(`local ${opB}=${n.code}[${n.ip}]`);
    lines.push(`${n.ip}=${n.ip}+1`);
    lines.push(handlerXorKey ? `local ${hB}=${n.handlers}[bit32.bxor(${opB},${hxk})]` : `local ${hB}=${n.handlers}[${opB}]`);
    lines.push(`${dv1}=bit32.bxor(${dv1},${opB})`);
    lines.push(`${lastOp}=${opB}`);
    lines.push(`if type(${hB})=="function" then ${hB}() end`);
    lines.push(`end`);

    lines.push(`${stateAcc}=bit32.lrotate(bit32.bxor(${stateAcc},${lastOp}),${rotAmt})`);

    lines.push(`${ipMask}=bit32.lrotate(bit32.bxor(${ipMask},${lastOp}),${ipRotAmt})`);
    lines.push(`${n.ip}=bit32.bxor(${n.ip},${ipMask})`);

    lines.push(`if bit32.band(${stateAcc},0xFFFFFFFF)==${toHexInt(decoyVal)} then ${n.ip}=1;${stateAcc}=0 end`);

    lines.push(`${cycleVar}=${cycleVar}+1`);
    lines.push(`if bit32.band(${cycleVar},${toHexInt(switchMask)})==${switchThresh} then ${dispMode}=1-${dispMode} end`);

    lines.push(handlerXorKey
      ? `if bit32.band(${cycleVar},0xFFF)==0 then local _mi=bit32.band(${cycleVar},0x3F);local _xmi=bit32.bxor(_mi,${hxk});local _oh=${origVar}[_xmi];if _oh then ${n.handlers}[_xmi]=function() _oh() end;${n.handlers}[_xmi+128]=${n.handlers}[_xmi] end end`
      : `if bit32.band(${cycleVar},0xFFF)==0 then local _mi=bit32.band(${cycleVar},0x3F);local _oh=${origVar}[_mi];if _oh then ${n.handlers}[_mi]=function() _oh() end;${n.handlers}[_mi+128]=${n.handlers}[_mi] end end`);

    const ahMask = [0x1FFF, 0x3FFF, 0x0FFF][Math.floor(rng() * 3)];
    lines.push(`if bit32.band(${cycleVar},${toHexInt(ahMask)})==0 and ${cycleVar}>0 then`);
    lines.push(`for _sk,_sv in pairs(${sigTable}) do if tostring(_sk)~=_sv then ${detFlag}=${detFlag}+1 end end`);

    const rtV = randomName(2);
    const rtWork = 100 + Math.floor(rng() * 200);
    lines.push(`do local ${rtV}=(type(tick)=="function" and tick()) or 0`);
    lines.push(`local _s=0;for _i=1,${rtWork} do _s=bit32.bxor(_s,_i) end`);
    lines.push(`local _t2=(type(tick)=="function" and tick()) or 0`);
    lines.push(`if ${rtV}>0 and _t2-${rtV}>0.05 then ${detFlag}=${detFlag}+1 end end`);
    lines.push(`end`);

    lines.push(`if ${detFlag}>1 then ${punishDelay}=${punishDelay}+1 end`);
    const punishThresh = 100 + Math.floor(rng() * 400);
    lines.push(`if ${punishDelay}>${punishThresh} and bit32.band(${cycleVar},0xFF)==0 then`);

    lines.push(`local _rk=bit32.band(${stateAcc},0x7F)`);
    lines.push(handlerXorKey
      ? `local _xrk=bit32.bxor(_rk,${hxk});if ${n.handlers}[_xrk] then ${n.handlers}[_xrk]=function() end end`
      : `if ${n.handlers}[_rk] then ${n.handlers}[_rk]=function() end end`);
    lines.push(`end`);

    const cfiExpect = (0xDEAD0000 | Math.floor(rng() * 0xFFFF)) >>> 0;
    lines.push(`if bit32.band(${stateAcc},0xFFFFFFFF)==${toHexInt(cfiExpect)} then ${n.ip}=1;${detFlag}=${detFlag}+99 end`);

    lines.push(`${dv2}=bit32.bxor(${n.stackTop},bit32.band(${stateAcc},0xFF))`);

    lines.push(`end`);

    const fakeOp = randomName(2);
    const fakeH = randomName(3);
    const fakeHandlerTable = randomName(4);
    lines.push(`if type(${n.handlers})=="number" then`);
    lines.push(`local ${fakeHandlerTable}={}`);
    lines.push(`for _fk,_fv in pairs(${n.handlers}) do ${fakeHandlerTable}[bit32.bxor(_fk,${toHexInt(S_DEAD1)})]=${n.handlers}[_fk] end`);
    lines.push(`while ${n.ip}<=#${n.code} do local ${fakeOp}=bit32.bxor(${n.code}[${n.ip}],${toHexInt(S_DEAD2)});${n.ip}=${n.ip}+1;local ${fakeH}=${fakeHandlerTable}[${fakeOp}];if ${fakeH} then ${fakeH}() end end`);
    lines.push(`end`);

    lines.push(`${stVar}=${S_DEAD3}`);
    lines.push(`end`);
    lines.push(`end`);
  } else {
    lines.push(`while true do`);
    lines.push(`if ${n.doReturn} or ${n.ip}>#${n.code} then break end`);
    lines.push(`local op=${n.code}[${n.ip}]`);
    lines.push(`${n.ip}=${n.ip}+1`);
    lines.push(`local h=${n.handlers}[op]`);
    lines.push(`if h then h() end`);
    lines.push(`end`);
  }

  lines.push(`if ${n.tailFn} then return ${n.tailFn}(table.unpack(${n.tailArgs},1,${n.tailN})) end`);

  if (level === "max") {

    lines.push(`if not ${n.initLocals} and not next(${n.upvalues}) then`);
    lines.push(`for _zi=1,#${n.code} do ${n.code}[_zi]=0 end`);
    lines.push(`for _zi=1,#${n.K} do ${n.K}[_zi]=0 end`);
    lines.push(`for _zi=1,#${n.locals} do ${n.locals}[_zi]=nil end`);
    lines.push(`for _zi=1,#${n.protos} do ${n.protos}[_zi]=nil end`);
    lines.push(`end`);
  }

  if (doPooling) {

    const rvVar = randomName(3);
    lines.push(`local ${rvVar}=nil`);
    lines.push(`if ${n.doReturn} then`);
    lines.push(`if ${n.retPack} then ${rvVar}=${n.retPack}`);
    lines.push(`elseif ${n.retFromStack} and ${n.retN}>0 then ${rvVar}=table.pack(table.unpack(${n.stack},${n.retBase}+1,${n.retTop}))`);
    lines.push(`end end`);

    lines.push(`for _i=1,${n.stackTop} do ${n.stack}[_i]=nil end`);
    lines.push(`for _k in next,${n.locals} do ${n.locals}[_k]=nil end`);
    lines.push(`for _i=1,${n.callBaseTop} do ${n.callBases}[_i]=nil end`);
    lines.push(`if #${poolStk}<${poolMax} then ${poolStk}[#${poolStk}+1]=${n.stack} end`);
    lines.push(`if #${poolLoc}<${poolMax} then ${poolLoc}[#${poolLoc}+1]=${n.locals} end`);
    lines.push(`if #${poolCb}<${poolMax} then ${poolCb}[#${poolCb}+1]=${n.callBases} end`);

    lines.push(`if ${rvVar} then return table.unpack(${rvVar},1,${rvVar}.n or #${rvVar}) end`);
    lines.push(`if ${n.doReturn} then return end`);
    lines.push(`return nil`);
    lines.push(`end`);
  } else {
    lines.push(`if ${n.doReturn} then`);
    lines.push(`if ${n.retPack} then return table.unpack(${n.retPack},1,${n.retPack}.n or #${n.retPack}) end`);
    lines.push(`if ${n.retFromStack} then`);
    lines.push(`if ${n.retN}==0 then return end`);
    lines.push(`return table.unpack(${n.stack},${n.retBase}+1,${n.retTop})`);
    lines.push(`end`);
    lines.push(`return`);
    lines.push(`end`);
    lines.push(`return nil`);
    lines.push(`end`);
  }

  if (level === "max") {
    const builtinDefs: [string, string][] = [

      ["table.unpack", randomName(3)],
      ["table.insert", randomName(3)],
      ["table.concat", randomName(3)],
      ["table.pack", randomName(3)],
      ["table.remove", randomName(3)],
      ["string.char", randomName(3)],
      ["string.byte", randomName(3)],
      ["string.len", randomName(3)],
      ["bit32.lrotate", randomName(3)],
      ["bit32.rshift", randomName(3)],
      ["bit32.bxor", randomName(3)],
      ["bit32.band", randomName(3)],
      ["bit32.bor", randomName(3)],
      ["math.floor", randomName(3)],
      ["math.huge", randomName(3)],
      ["math.min", randomName(3)],
      ["math.max", randomName(3)],
      ["math.abs", randomName(3)],
      ["math.pi", randomName(3)],

      ["getmetatable", randomName(3)],
      ["setmetatable", randomName(3)],
      ["tostring", randomName(3)],
      ["tonumber", randomName(3)],
      ["rawequal", randomName(3)],
      ["rawget", randomName(3)],
      ["rawset", randomName(3)],
      ["rawlen", randomName(3)],
      ["typeof", randomName(3)],
      ["xpcall", randomName(3)],
      ["pcall", randomName(3)],
      ["ipairs", randomName(3)],
      ["pairs", randomName(3)],
      ["error", randomName(3)],
      ["select", randomName(3)],
      ["unpack", randomName(3)],
      ["next", randomName(3)],
      ["type", randomName(3)],
    ];

    builtinDefs.sort((a, b) => b[0].length - a[0].length);

    const aliasDefs: string[] = builtinDefs.map(([b, a]) => {
      if (b.includes('.')) {
        const [lib, method] = b.split('.');
        return `local ${a}=${n.env}[${luaEsc(lib)}][${luaEsc(method)}]`;
      }
      return `local ${a}=${n.env}[${luaEsc(b)}]`;
    });

    for (let li = 1; li < lines.length; li++) {
      for (const [builtin, alias] of builtinDefs) {
        if (lines[li].includes(builtin)) {
          lines[li] = lines[li].split(builtin).join(alias);
        }
      }
    }

    const stringLiterals: [string, string][] = [
      ['"function"', luaEsc("function")],
      ['"table"', luaEsc("table")],
      ['"number"', luaEsc("number")],
      ['"string"', luaEsc("string")],
      ['"boolean"', luaEsc("boolean")],
      ['"userdata"', luaEsc("userdata")],
      ['"nil"', luaEsc("nil")],
      ['.__index', `[${luaEsc("__index")}]`],
      ['.__newindex', `[${luaEsc("__newindex")}]`],
      ['.__call', `[${luaEsc("__call")}]`],
      ['.__iter', `[${luaEsc("__iter")}]`],
      ['.__add', `[${luaEsc("__add")}]`],
      ['.__sub', `[${luaEsc("__sub")}]`],
      ['.__mul', `[${luaEsc("__mul")}]`],
      ['.__div', `[${luaEsc("__div")}]`],
      ['.__mod', `[${luaEsc("__mod")}]`],
      ['.__pow', `[${luaEsc("__pow")}]`],
      ['.__unm', `[${luaEsc("__unm")}]`],
      ['.__eq', `[${luaEsc("__eq")}]`],
      ['.__lt', `[${luaEsc("__lt")}]`],
      ['.__le', `[${luaEsc("__le")}]`],
      ['.__len', `[${luaEsc("__len")}]`],
      ['.__concat', `[${luaEsc("__concat")}]`],
      ['.__tostring', `[${luaEsc("__tostring")}]`],
      ['"__index"', luaEsc("__index")],
      ['"__newindex"', luaEsc("__newindex")],
      ['"__call"', luaEsc("__call")],
      ['"__iter"', luaEsc("__iter")],
      ['"__add"', luaEsc("__add")],
      ['"__sub"', luaEsc("__sub")],
      ['"__mul"', luaEsc("__mul")],
      ['"__div"', luaEsc("__div")],
      ['"__mod"', luaEsc("__mod")],
      ['"__pow"', luaEsc("__pow")],
      ['"__unm"', luaEsc("__unm")],
      ['"__eq"', luaEsc("__eq")],
      ['"__lt"', luaEsc("__lt")],
      ['"__le"', luaEsc("__le")],
      ['"__len"', luaEsc("__len")],
      ['"__concat"', luaEsc("__concat")],
      ['"__tostring"', luaEsc("__tostring")],
    ];

    stringLiterals.sort((a, b) => b[0].length - a[0].length);
    for (let li = 1; li < lines.length; li++) {
      for (const [orig, encoded] of stringLiterals) {
        if (lines[li].includes(orig)) {
          lines[li] = lines[li].split(orig).join(encoded);
        }
      }
    }

    lines.splice(1, 0, ...aliasDefs);
  }

  return lines.join("\n");
}

export type VMGenLevel = "debug" | "normal" | "max";

export type FeatureFlag =
  | "fakeHandlers" | "opaquePredicates" | "cff"
  | "handlerMutation" | "handlerNoise" | "antiDebug"
  | "antiTamper" | "superOperators" | "constantFolding"
  | "minification" | "stringFragment" | "lazyDecode" | "nopCamouflage" | "contextOpcodes" | "nonLinearJumps"
  | "antiHookDeep" | "antiDump" | "sandboxDetect" | "cfi" | "runtimeMonitor"
  | "stringMutation" | "adaptiveFragments" | "stackPooling";

export interface VMGenOptions {

  level?: VMGenLevel;

  executorGlobals?: boolean;

  nesting?: number;

  vmId?: string;

  polymorphicSeed?: number;

  disableFeatures?: FeatureFlag[];

  forceSingleVM?: boolean;

  forceNestedVM?: boolean;

  _noWatermark?: boolean;

  forceFeatures?: FeatureFlag[];

  noCompression?: boolean;
}

function featureEnabled(options: VMGenOptions, flag: FeatureFlag, levelDefault: boolean): boolean {
  if (options.disableFeatures?.includes(flag)) return false;
  if (options.forceFeatures?.includes(flag)) return true;
  return levelDefault;
}

export function generateVM(chunk: BytecodeChunk, options: VMGenOptions = {}): string {
  const nesting = options.nesting ?? 0;

  const seed = options.polymorphicSeed || (Date.now() ^ (Math.random() * 0xFFFFFFFF));
  seedRandom(seed);

  if (nesting > 0 && !options.forceSingleVM) {
    const innerSeed = (seed * 2654435761) >>> 0;
    const outerSeed = (seed * 2246822519) >>> 0;
    const vmId = options.vmId ?? "nested";

    console.log(`[telemetry:${vmId}] Generating inner VM (seed=${innerSeed})...`);
    const t0 = Date.now();

    const safeInnerFeatures: FeatureFlag[] = [
      "superOperators", "constantFolding", "stringFragment",
    ];
    const innerForced: FeatureFlag[] = [];
    for (const f of safeInnerFeatures) {
      if (rng() > 0.4) innerForced.push(f);
    }

    const innerVM = generateVM(chunk, {
      level: "normal",
      nesting: 0,
      vmId: "inner",
      polymorphicSeed: innerSeed,
      executorGlobals: true,
      _noWatermark: true,
      disableFeatures: [
        "fakeHandlers", "opaquePredicates", "cff",
        "handlerMutation", "handlerNoise", "antiDebug",
        "antiTamper", "lazyDecode", "nopCamouflage", "minification", "contextOpcodes", "nonLinearJumps",
        "antiHookDeep", "antiDump", "sandboxDetect", "cfi", "runtimeMonitor",
        "stringMutation", "adaptiveFragments", "stackPooling",
      ],
      forceFeatures: innerForced,
    });
    const t1 = Date.now();
    console.log(`[telemetry:inner] inner_vm_size: ${innerVM.length} chars (${t1 - t0}ms)`);

    try {
      console.log(`[telemetry:${vmId}] Compiling inner VM to bytecode...`);
      const innerChunk = compileString(innerVM);
      const t2 = Date.now();
      console.log(`[telemetry:inner] inner_compile: ${t2 - t1}ms, ${innerChunk.code.length} instructions, ${innerChunk.K.length} constants, ${(innerChunk.protos || []).length} protos`);

      console.log(`[telemetry:${vmId}] Generating outer VM (seed=${outerSeed})...`);
      const outerVM = generateVM(innerChunk, {
        level: "max",
        nesting: 0,
        vmId: "outer",
        polymorphicSeed: outerSeed,
        executorGlobals: true,
      });
      const t3 = Date.now();
      console.log(`[telemetry:outer] outer_vm_size: ${outerVM.length} chars (${t3 - t2}ms)`);
      console.log(`[telemetry:${vmId}] Total nested VM: ${outerVM.length} chars (${t3 - t0}ms)`);
      if (outerVM.length > 800000) {
        console.warn(`[telemetry:${vmId}] WARNING: output > 800KB (${outerVM.length})`);
      }
      console.log(`[telemetry:${vmId}] compile_errors: 0, fallback_used: false`);
      return outerVM;
    } catch (e: any) {
      console.error(`[telemetry:${vmId}] compileString FAILED: ${e.message}`);
      if (options.forceNestedVM) {
        throw new Error(`[VM-in-VM] Inner compilation failed and forceNestedVM is set: ${e.message}`);
      }

      console.warn(`[telemetry:${vmId}] Falling back to single VM (max level)`);
      console.log(`[telemetry:${vmId}] compile_errors: 1, fallback_used: true`);
      seedRandom(outerSeed);
      return generateVM(chunk, {
        level: "max",
        nesting: 0,
        vmId: "fallback",
        polymorphicSeed: outerSeed,
        executorGlobals: options.executorGlobals,
      });
    }
  }

  const level = options.level ?? "normal";
  const includeExecutor = options.executorGlobals ?? (level !== "debug");
  const doShuffle = level !== "debug";
  const encodeStrings = level !== "debug";
  const doMinify = featureEnabled(options, "minification", level === "max");
  const xorKey = encodeStrings ? (1 + Math.floor(rng() * 254)) : 0;
  const xorStep = encodeStrings ? (1 + Math.floor(rng() * 254)) : 0;
  const codeXorKey = (level !== "debug") ? (1 + Math.floor(rng() * 254)) : 0;
  const doFragment = featureEnabled(options, "stringFragment", level === "max");
  const doConstantFold = featureEnabled(options, "constantFolding", level === "max");
  const doLazyDecode = featureEnabled(options, "lazyDecode", level === "max");
  const lazyBaseKey = doLazyDecode ? ((Math.floor(rng() * 0xFFFFFFFF) + 1) >>> 0) : 0;
  const lazyKeyPrime = doLazyDecode ? ((Math.floor(rng() * 0x7FFFFFFF) * 2 + 1) >>> 0) : 0;
  const doContextOps = featureEnabled(options, "contextOpcodes", level === "max");
  const ctxInit = doContextOps ? ((Math.floor(rng() * 0xFFFFFFFF) + 1) >>> 0) : 0;
  const ctxPrime = doContextOps ? ((Math.floor(rng() * 0xFFFFFFFF) | 1) >>> 0) : 0;
  const doNonLinearJumps = featureEnabled(options, "nonLinearJumps", level === "max");
  const jumpKey = doNonLinearJumps ? (1 + Math.floor(rng() * 0xFFFE)) : 0;

  if (featureEnabled(options, "superOperators", level === "max")) {
    fuseChunk(chunk);
  }

  if (featureEnabled(options, "nopCamouflage", level === "max")) {
    injectCamouflageChunk(chunk);
  }

  if (level === "max") {
    flattenChunk(chunk);
  }

  if (doContextOps) {
    contextTransformChunk(chunk, ctxInit, ctxPrime);
  }

  if (doNonLinearJumps) {
    encodeJumpTargetsChunk(chunk, jumpKey);
  }

  resetNames();

  const { encode: opcodeEncode } = shuffleOpcodes(doShuffle);

  const mappedCode = doShuffle ? mapBytecode(chunk.code, opcodeEncode) : chunk.code;

  const n = createNames(level);

  const envSetup = buildEnvSetup(n, level, includeExecutor);

  const codeHash = featureEnabled(options, "antiTamper", level === "max") ? computeCodeHash(mappedCode) : 0;

  const protoKeys = level === "max" ? {
    pK: randomName(2), pC: randomName(2), pP: randomName(2),
    pU: randomName(2), pN: randomName(2)
  } : { pK: "K", pC: "C", pP: "P", pU: "U", pN: "nParams" };

  const doMultiLayer = level === "max";
  const cipherSeeds: [number, number, number] | undefined = doMultiLayer ? [
    (Math.floor(rng() * 0x3FFFFFFE) + 3) >>> 0,
    (Math.floor(rng() * 0xFFFF) + 1) >>> 0,
    (Math.floor(rng() * 0xFF) + 1) >>> 0,
  ] : undefined;

  const effectiveCodeXorKey = doMultiLayer ? 0 : codeXorKey;

  const doMutation = featureEnabled(options, "stringMutation", level === "max") && doLazyDecode;

  const doPooling = featureEnabled(options, "stackPooling", level === "max");

  const doStringPools = level === "max" && doLazyDecode;
  const poolsVarName = doStringPools ? randomName(3) : "";

  const vmFunction = buildVMFunction(n, opcodeEncode, level, encodeStrings, xorKey, xorStep, effectiveCodeXorKey, codeHash, lazyBaseKey, lazyKeyPrime, ctxInit, ctxPrime, jumpKey, protoKeys, cipherSeeds, doMutation, doPooling, poolsVarName);

  const honeypotPool = [
    "RemoteEvent","FireServer","InvokeServer","OnServerEvent","OnClientEvent",
    "HttpService","GetAsync","PostAsync","JSONDecode","JSONEncode",
    "DataStoreService","GetDataStore","SetAsync","UpdateAsync","RemoveAsync",
    "Players","LocalPlayer","Character","Humanoid","WalkSpeed",
    "MarketplaceService","PromptPurchase","ProcessReceipt",
    "TeleportService","Teleport","TeleportToPlaceInstance",
    "ReplicatedStorage","ServerStorage","ServerScriptService",
    "UserInputService","InputBegan","InputEnded","GetMouse",
    "RunService","Heartbeat","RenderStepped","Stepped",
    "Workspace","CurrentCamera","FindFirstChild","WaitForChild",
    "GetChildren","GetDescendants","IsA","Clone","Destroy",
    "Instance","new","CFrame","Vector3","UDim2","Color3",
    "game","script","require","warn","error","print",
    "coroutine","spawn","delay","wait","task",
    "pcall","xpcall","rawget","rawset","setmetatable","getmetatable",
    "string","table","math","bit32","utf8","os","debug",
    "loadstring","getfenv","setfenv","newproxy",
  ];
  let extendedK = chunk.K;
  if (level === "max" && doLazyDecode) {
    extendedK = [...chunk.K];
    const nHoneypots = 5 + Math.floor(rng() * 11);
    const shuffledPool = [...honeypotPool];
    for (let i = shuffledPool.length - 1; i > 0; i--) {
      const j = Math.floor(rng() * (i + 1));
      [shuffledPool[i], shuffledPool[j]] = [shuffledPool[j], shuffledPool[i]];
    }

    for (let i = 0; i < nHoneypots; i++) {
      const roll = rng();
      if (roll < 0.7 && i < shuffledPool.length) {
        extendedK.push(shuffledPool[i]);
      } else if (roll < 0.85) {
        extendedK.push(Math.floor(rng() * 1000));
      } else {
        extendedK.push(rng() > 0.5);
      }
    }
  }

  let finalK: any[] = extendedK;
  let poolsSerialized = "";
  if (doStringPools) {
    const { processedK, pools } = buildStringPools(extendedK, lazyBaseKey, lazyKeyPrime, doMutation);
    finalK = processedK;

    const poolParts = pools.map(p => `{${p.join(",")}}`);
    poolsSerialized = `{${poolParts.join(",")}}`;
    console.log(`[§69] String pools: ${pools.length} pools, ${pools.reduce((a, p) => a + p.length, 0)} total bytes`);
  }

  const dataK = serializeConstants(finalK, encodeStrings, xorKey, doLazyDecode ? false : doFragment, xorStep, doConstantFold, lazyBaseKey, lazyKeyPrime, doMutation);
  const dataP = serializeProtos(chunk.protos, opcodeEncode, encodeStrings, doShuffle, xorKey, doLazyDecode ? false : doFragment, xorStep, effectiveCodeXorKey, doConstantFold, lazyBaseKey, lazyKeyPrime, level === "max", protoKeys, cipherSeeds, doMutation);

  const dK = randomName(3);
  const dC = randomName(3);
  const dP = randomName(3);
  const parts: string[] = [];
  parts.push(envSetup);
  parts.push(vmFunction);

  if (doStringPools && poolsSerialized) {
    parts.push(`${poolsVarName}=${poolsSerialized}`);
  }

  if (doMultiLayer && cipherSeeds) {

    const dataC = packCodeToTable(mappedCode, cipherSeeds[0], cipherSeeds[1], cipherSeeds[2]);
    const dataDecls = [
      `local ${dK}=${dataK}`,
      `local ${dC}=${dataC}`,
      `local ${dP}=${dataP}`,
    ];

    const declOrder = [0, 1, 2];
    for (let di = declOrder.length - 1; di > 0; di--) {
      const dj = Math.floor(rng() * (di + 1));
      [declOrder[di], declOrder[dj]] = [declOrder[dj], declOrder[di]];
    }
    for (const idx of declOrder) parts.push(dataDecls[idx]);
  } else {

    const dataC = serializeCode(mappedCode, effectiveCodeXorKey);
    const dataDecls = [
      `local ${dK}=${dataK}`,
      `local ${dC}=${dataC}`,
      `local ${dP}=${dataP}`,
    ];
    const declOrder = [0, 1, 2];
    for (let di = declOrder.length - 1; di > 0; di--) {
      const dj = Math.floor(rng() * (di + 1));
      [declOrder[di], declOrder[dj]] = [declOrder[dj], declOrder[di]];
    }
    for (const idx of declOrder) parts.push(dataDecls[idx]);
  }
  parts.push(`return ${n.run}(${dK},${dC},${n.env},${dP})`);

  let output = parts.join("\n");

  output = output.replace(/;/g, "\n");

  if (doMinify) {
    output = minify(output);
  }

  if (level === "max") {
    output = wrapCustomCipher(output);
  }

  if (level === "max") {
    output = wrapNestedVM(output);
  }

  if (level === "max" && !options.noCompression) {
    output = wrapStubVM(output);
  }

  if (!options._noWatermark) {

    const buildTS = Math.floor(Date.now() / 1000) & 0xFFFFFFFF;
    const buildRand = Math.floor(Math.random() * 0xFFFF);
    const fingerprint = ((buildTS ^ (buildRand << 16)) >>> 0);
    const fpHex = fingerprint.toString(16).padStart(8, '0').toUpperCase();

    const artLines = [
      `   ___ _         _       ___         _          _   _           __   ___ `,
      `  / __| |_  _ __| |___  | _ \\_ _ ___| |_ ___ __| |_(_)___ _ _   \\ \\ / / |`,
      ` | (__| | || / _\` / -_) |  _/ '_/ _ \\  _/ -_) _|  _| / _ \\ ' \\   \\ V /| |`,
      `  \\___|_|\\_, \\__,_\\___| |_| |_| \\___/\\__\\___\\__|\\__|_\\___/_||_|   \\_/ |_|`,
      `         |__/`,
      ``,
      `  https://clydeprotectionde.cloud`,
      `  build ${fpHex}`,
    ];

    for (let li = 0; li < 8 && li < artLines.length; li++) {
      const nibble = (fingerprint >>> (28 - li * 4)) & 0xF;

      const spaces = (nibble & 3) + 1;
      artLines[li] = artLines[li].trimEnd() + ' '.repeat(spaces);
    }

    const watermark = `--[[\n${artLines.join('\n')}\n]]\n`;
    output = watermark + output;
  }

  return output;
}
