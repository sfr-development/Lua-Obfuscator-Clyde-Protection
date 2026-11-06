import type {
  Chunk,
  Statement,
  LastStatement,
  Expression,
  Var,
  Identifier,
  MemberExpression,
  IndexExpression,
  CallExpression,
  MethodCallExpression,
  Param,
  FuncName,
  TableField,
} from "../ast/types.js";
import type { RegBytecodeChunk, Constant } from "./bytecode.js";
import {
  RegOp, RK_OFFSET, RK,
  regEmit, regPatch, regPC, regAddConst,
  createRegChunk, regAddProto,
} from "./bytecode.js";

interface LoopCtx {
  breakPatches: number[];
  continuePatches: number[];
  bodyRegStart: number;
}

interface UpvalueRef {
  name: string;
  isLocal: boolean;
  index: number;
}

interface ScopeSnapshot {
  locals: Map<string, number>;
  nextReg: number;
  freeReg: number;
}

interface Ctx {
  chunk: RegBytecodeChunk;
  locals: Map<string, number>;
  nextReg: number;
  freeReg: number;
  loopStack: LoopCtx[];
  parent?: Ctx;
  upvalues: Map<string, number>;
  upvalueList: UpvalueRef[];
  isVararg: boolean;
  nParams: number;
  uid: number;
}

function createCtx(parent?: Ctx): Ctx {
  return {
    chunk: createRegChunk(),
    locals: new Map(),
    nextReg: 0,
    freeReg: 0,
    loopStack: [],
    parent,
    upvalues: new Map(),
    upvalueList: [],
    isVararg: false,
    nParams: 0,
    uid: 0,
  };
}

function allocLocal(ctx: Ctx, name: string): number {
  const reg = ctx.nextReg++;
  ctx.locals.set(name, reg);
  if (ctx.freeReg < ctx.nextReg) ctx.freeReg = ctx.nextReg;
  ctx.chunk.maxRegs = Math.max(ctx.chunk.maxRegs, ctx.nextReg);
  return reg;
}

function allocHidden(ctx: Ctx, hint: string): number {
  return allocLocal(ctx, `\0${hint}_${ctx.uid++}`);
}

function allocTemp(ctx: Ctx): number {
  const reg = ctx.freeReg++;
  ctx.chunk.maxRegs = Math.max(ctx.chunk.maxRegs, ctx.freeReg);
  return reg;
}

function reserveRegs(ctx: Ctx, base: number, n: number): void {
  const need = base + n;
  if (ctx.freeReg < need) ctx.freeReg = need;
  ctx.chunk.maxRegs = Math.max(ctx.chunk.maxRegs, need);
}

function saveFree(ctx: Ctx): number { return ctx.freeReg; }
function restoreFree(ctx: Ctx, s: number): void { ctx.freeReg = s; }

function pushScope(ctx: Ctx): ScopeSnapshot {
  return { locals: new Map(ctx.locals), nextReg: ctx.nextReg, freeReg: ctx.freeReg };
}

function popScope(ctx: Ctx, snap: ScopeSnapshot): void {
  ctx.locals = snap.locals;
  ctx.nextReg = snap.nextReg;
  ctx.freeReg = snap.freeReg;
}

function pushLoop(ctx: Ctx, bodyRegStart: number): LoopCtx {
  const lc: LoopCtx = { breakPatches: [], continuePatches: [], bodyRegStart };
  ctx.loopStack.push(lc);
  return lc;
}

function popLoop(ctx: Ctx): void {
  const lc = ctx.loopStack.pop();
  if (lc) {
    const end = regPC(ctx.chunk);
    for (const pc of lc.breakPatches) patchJump(ctx, pc, end);
  }
}

function resolveContinues(ctx: Ctx): void {
  const lc = ctx.loopStack[ctx.loopStack.length - 1];
  if (lc) {
    const target = regPC(ctx.chunk);
    for (const pc of lc.continuePatches) patchJump(ctx, pc, target);
    lc.continuePatches = [];
  }
}

function currentLoop(ctx: Ctx): LoopCtx | undefined {
  return ctx.loopStack[ctx.loopStack.length - 1];
}

function resolveUpvalue(ctx: Ctx, name: string): number | null {
  const existing = ctx.upvalues.get(name);
  if (existing !== undefined) return existing;
  if (!ctx.parent) return null;

  const parentLocal = ctx.parent.locals.get(name);
  if (parentLocal !== undefined) {
    const idx = ctx.upvalueList.length;
    ctx.upvalueList.push({ name, isLocal: true, index: parentLocal });
    ctx.upvalues.set(name, idx);
    return idx;
  }

  const parentUV = resolveUpvalue(ctx.parent, name);
  if (parentUV !== null) {
    const idx = ctx.upvalueList.length;
    ctx.upvalueList.push({ name, isLocal: false, index: parentUV });
    ctx.upvalues.set(name, idx);
    return idx;
  }

  return null;
}

function emitJump(ctx: Ctx): number {
  const pc = regPC(ctx.chunk);
  regEmit(ctx.chunk, RegOp.JMP, 0, 0, 0);
  return pc;
}

function patchJump(ctx: Ctx, jmpPC: number, targetPC: number): void {
  regPatch(ctx.chunk, jmpPC * 4, 'B', targetPC - jmpPC - 1);
}

function constRK(ctx: Ctx, value: Constant): number {
  const ki = regAddConst(ctx.chunk, value);
  if (ki < RK_OFFSET) return RK(ki);
  const tmp = allocTemp(ctx);
  regEmit(ctx.chunk, RegOp.LOADKX, tmp);
  regEmit(ctx.chunk, RegOp.EXTRAARG, ki, 0, 0);
  return tmp;
}

function isCallLike(e: Expression): boolean {
  return e.type === "CallExpression" || e.type === "MethodCallExpression";
}

function hasSpread(args: Expression[]): boolean {
  if (args.length === 0) return false;
  const last = args[args.length - 1];
  return isCallLike(last) || last.type === "VarargExpression";
}

function compileExpr(ctx: Ctx, exp: Expression, dest: number): number {
  if (!exp) {
    if (dest === -1) dest = allocTemp(ctx);
    regEmit(ctx.chunk, RegOp.LOADNIL, dest, 0);
    return dest;
  }
  const c = ctx.chunk;

  switch (exp.type) {
    case "NilLiteral": {
      if (dest === -1) dest = allocTemp(ctx);
      regEmit(c, RegOp.LOADNIL, dest, 0);
      return dest;
    }
    case "BooleanLiteral": {
      if (dest === -1) dest = allocTemp(ctx);
      regEmit(c, RegOp.LOADBOOL, dest, exp.value ? 1 : 0, 0);
      return dest;
    }
    case "NumberLiteral": {
      if (dest === -1) dest = allocTemp(ctx);
      regEmit(c, RegOp.LOADK, dest, regAddConst(c, Number(exp.value)));
      return dest;
    }
    case "StringLiteral": {
      if (dest === -1) dest = allocTemp(ctx);
      regEmit(c, RegOp.LOADK, dest, regAddConst(c, exp.value));
      return dest;
    }

    case "Identifier": {
      if (exp.name === "nil") {
        if (dest === -1) dest = allocTemp(ctx);
        regEmit(c, RegOp.LOADNIL, dest, 0);
        return dest;
      }
      if (exp.name === "true" || exp.name === "false") {
        if (dest === -1) dest = allocTemp(ctx);
        regEmit(c, RegOp.LOADBOOL, dest, exp.name === "true" ? 1 : 0, 0);
        return dest;
      }
      const localReg = ctx.locals.get(exp.name);
      if (localReg !== undefined) {
        if (dest === -1) return localReg;
        if (dest !== localReg) regEmit(c, RegOp.MOVE, dest, localReg);
        return dest;
      }
      const uv = resolveUpvalue(ctx, exp.name);
      if (uv !== null) {
        if (dest === -1) dest = allocTemp(ctx);
        regEmit(c, RegOp.GETUPVAL, dest, uv);
        return dest;
      }
      if (dest === -1) dest = allocTemp(ctx);
      regEmit(c, RegOp.GETGLOBAL, dest, regAddConst(c, exp.name));
      return dest;
    }

    case "BinaryExpression":
      return compileBinaryExpr(ctx, exp, dest);

    case "UnaryExpression": {
      if (dest === -1) dest = allocTemp(ctx);
      const s = saveFree(ctx);
      const operand = compileExpr(ctx, exp.argument, -1);
      switch (exp.operator) {
        case "not": regEmit(c, RegOp.NOT, dest, operand); break;
        case "-":   regEmit(c, RegOp.UNM, dest, operand); break;
        case "#":   regEmit(c, RegOp.LEN, dest, operand); break;
      }
      restoreFree(ctx, s);
      return dest;
    }

    case "ParenExpression":
      return compileExpr(ctx, exp.expression, dest);

    case "TypeAssertion":
      return compileExpr(ctx, exp.expression, dest);

    case "CallExpression": {
      if (dest === -1) dest = allocTemp(ctx);
      compileCall(ctx, exp, dest, 2);
      return dest;
    }

    case "MethodCallExpression": {
      if (dest === -1) dest = allocTemp(ctx);
      compileMethodCall(ctx, exp, dest, 2);
      return dest;
    }

    case "IndexExpression": {
      if (dest === -1) dest = allocTemp(ctx);
      const s = saveFree(ctx);
      const obj = compileExpr(ctx, exp.object, -1);
      const key = compileExprRK(ctx, exp.index);
      regEmit(c, RegOp.GETTABLE, dest, obj, key);
      restoreFree(ctx, s);
      return dest;
    }

    case "MemberExpression": {
      if (dest === -1) dest = allocTemp(ctx);
      const s = saveFree(ctx);
      const obj = compileExpr(ctx, exp.object, -1);
      const key = constRK(ctx, exp.property);
      regEmit(c, RegOp.GETTABLE, dest, obj, key);
      restoreFree(ctx, s);
      return dest;
    }

    case "TableConstructor":
      return compileTableCtor(ctx, exp.fields, dest);

    case "VarargExpression": {
      if (dest === -1) dest = allocTemp(ctx);
      regEmit(c, RegOp.VARARG, dest, 2);
      return dest;
    }

    case "StringInterpolation":
      return compileStringInterp(ctx, exp.parts, dest);

    case "FunctionExpression": {
      if (dest === -1) dest = allocTemp(ctx);
      const protoIdx = compileFunctionBody(ctx, exp.params, exp.body);
      regEmit(c, RegOp.CLOSURE, dest, protoIdx);
      return dest;
    }

    case "IfElseExpression":
      return compileIfElseExpr(ctx, exp, dest);

    default: {
      if (dest === -1) dest = allocTemp(ctx);
      regEmit(c, RegOp.LOADNIL, dest, 0);
      return dest;
    }
  }
}

function compileBinaryExpr(ctx: Ctx, exp: any, dest: number): number {
  if (dest === -1) dest = allocTemp(ctx);
  const c = ctx.chunk;

  if (exp.operator === "and") {
    const s = saveFree(ctx);
    compileExpr(ctx, exp.left, dest);
    regEmit(c, RegOp.TEST, dest, 0, 0);
    const skip = emitJump(ctx);
    compileExpr(ctx, exp.right, dest);
    patchJump(ctx, skip, regPC(c));
    restoreFree(ctx, s);
    return dest;
  }

  if (exp.operator === "or") {
    const s = saveFree(ctx);
    compileExpr(ctx, exp.left, dest);
    regEmit(c, RegOp.TEST, dest, 0, 1);
    const skip = emitJump(ctx);
    compileExpr(ctx, exp.right, dest);
    patchJump(ctx, skip, regPC(c));
    restoreFree(ctx, s);
    return dest;
  }

  if (["==", "~=", "<", "<=", ">", ">="].includes(exp.operator)) {
    return compileComparison(ctx, exp, dest);
  }

  if (exp.operator === "..") {
    const s = saveFree(ctx);
    const regs = collectConcatChain(ctx, exp);
    regEmit(c, RegOp.CONCAT, dest, regs[0], regs[regs.length - 1]);
    restoreFree(ctx, s);
    return dest;
  }

  const arithOps: Record<string, RegOp> = {
    "+": RegOp.ADD, "-": RegOp.SUB, "*": RegOp.MUL, "/": RegOp.DIV,
    "%": RegOp.MOD, "^": RegOp.POW, "//": RegOp.IDIV,
  };
  const op = arithOps[exp.operator];
  if (op !== undefined) {
    const s = saveFree(ctx);
    const rb = compileExprRK(ctx, exp.left);
    const rc = compileExprRK(ctx, exp.right);
    regEmit(c, op, dest, rb, rc);
    restoreFree(ctx, s);
    return dest;
  }

  regEmit(c, RegOp.LOADNIL, dest, 0);
  return dest;
}

function compileComparison(ctx: Ctx, exp: any, dest: number): number {
  const c = ctx.chunk;
  const s = saveFree(ctx);
  const rb = compileExprRK(ctx, exp.left);
  const rc = compileExprRK(ctx, exp.right);

  let cmpOp: RegOp;
  let invertA: number;
  let swapped = false;

  switch (exp.operator) {
    case "==":  cmpOp = RegOp.EQ; invertA = 0; break;
    case "~=":  cmpOp = RegOp.EQ; invertA = 1; break;
    case "<":   cmpOp = RegOp.LT; invertA = 0; break;
    case "<=":  cmpOp = RegOp.LE; invertA = 0; break;
    case ">":   cmpOp = RegOp.LT; invertA = 0; swapped = true; break;
    case ">=":  cmpOp = RegOp.LE; invertA = 0; swapped = true; break;
    default:    cmpOp = RegOp.EQ; invertA = 0;
  }

  if (swapped) {
    regEmit(c, cmpOp, invertA, rc, rb);
  } else {
    regEmit(c, cmpOp, invertA, rb, rc);
  }

  const skip = emitJump(ctx);
  regEmit(c, RegOp.LOADBOOL, dest, 1, 1);
  patchJump(ctx, skip, regPC(c));
  regEmit(c, RegOp.LOADBOOL, dest, 0, 0);
  restoreFree(ctx, s);
  return dest;
}

function collectConcatChain(ctx: Ctx, exp: Expression): number[] {

  const exprs: Expression[] = [];
  function collect(e: Expression): void {
    if (e.type === "BinaryExpression" && (e as any).operator === "..") {
      collect((e as any).left);
      collect((e as any).right);
    } else {
      exprs.push(e);
    }
  }
  collect(exp);

  const base = ctx.freeReg;
  reserveRegs(ctx, base, exprs.length);

  for (let i = 0; i < exprs.length; i++) {
    compileExpr(ctx, exprs[i], base + i);
  }

  return exprs.map((_, i) => base + i);
}

function compileTableCtor(ctx: Ctx, fields: TableField[], dest: number): number {
  if (dest === -1) dest = allocTemp(ctx);
  const c = ctx.chunk;
  const s = saveFree(ctx);
  regEmit(c, RegOp.NEWTABLE, dest, 0, 0);

  let arrIdx = 0;
  for (let fi = 0; fi < fields.length; fi++) {
    const f = fields[fi];
    const isLast = fi === fields.length - 1;

    if (f.kind === "index") {
      const key = compileExprRK(ctx, f.index);
      const val = compileExprRK(ctx, f.value);
      regEmit(c, RegOp.SETTABLE, dest, key, val);
    } else if (f.kind === "named") {
      const key = constRK(ctx, f.name);
      const val = compileExprRK(ctx, f.value);
      regEmit(c, RegOp.SETTABLE, dest, key, val);
    } else {
      arrIdx++;
      if (isLast && (isCallLike(f.value) || f.value.type === "VarargExpression")) {

        const base = dest + 1;
        ctx.freeReg = Math.max(ctx.freeReg, base);
        if (isCallLike(f.value)) {
          compileCallMultiReg(ctx, f.value, base, 0);
        } else {
          regEmit(c, RegOp.VARARG, base, 0);
        }
        regEmit(c, RegOp.SETLIST, dest, 0, arrIdx);
      } else {
        const key = constRK(ctx, arrIdx);
        const val = compileExprRK(ctx, f.value);
        regEmit(c, RegOp.SETTABLE, dest, key, val);
      }
    }
  }

  restoreFree(ctx, s);
  if (dest >= ctx.freeReg) ctx.freeReg = dest + 1;
  return dest;
}

function compileStringInterp(ctx: Ctx, parts: (string | Expression)[], dest: number): number {
  if (dest === -1) dest = allocTemp(ctx);
  const c = ctx.chunk;

  if (parts.length === 0) {
    regEmit(c, RegOp.LOADK, dest, regAddConst(c, ""));
    return dest;
  }

  const s = saveFree(ctx);
  const base = ctx.freeReg;
  const count = parts.length;

  reserveRegs(ctx, base, count);

  for (let i = 0; i < count; i++) {
    const p = parts[i];
    if (typeof p === "string") {
      regEmit(c, RegOp.LOADK, base + i, regAddConst(c, p));
    } else {
      compileExpr(ctx, p, base + i);
    }
  }

  if (count === 1) {
    if (dest !== base) regEmit(c, RegOp.MOVE, dest, base);
  } else {
    regEmit(c, RegOp.CONCAT, dest, base, base + count - 1);
  }

  restoreFree(ctx, s);
  if (dest >= ctx.freeReg) ctx.freeReg = dest + 1;
  return dest;
}

function compileIfElseExpr(ctx: Ctx, exp: any, dest: number): number {
  if (dest === -1) dest = allocTemp(ctx);
  const c = ctx.chunk;
  const s = saveFree(ctx);
  const endJumps: number[] = [];

  const cond = compileExpr(ctx, exp.condition, -1);
  regEmit(c, RegOp.TEST, cond, 0, 0);
  const jmpElse = emitJump(ctx);
  compileExpr(ctx, exp.thenExp, dest);
  endJumps.push(emitJump(ctx));
  patchJump(ctx, jmpElse, regPC(c));

  if (exp.elseifClauses) {
    for (const clause of exp.elseifClauses) {
      const cr = compileExpr(ctx, clause.condition, -1);
      regEmit(c, RegOp.TEST, cr, 0, 0);
      const jNext = emitJump(ctx);
      compileExpr(ctx, clause.value, dest);
      endJumps.push(emitJump(ctx));
      patchJump(ctx, jNext, regPC(c));
    }
  }

  compileExpr(ctx, exp.elseExp, dest);
  for (const j of endJumps) patchJump(ctx, j, regPC(c));

  restoreFree(ctx, s);
  if (dest >= ctx.freeReg) ctx.freeReg = dest + 1;
  return dest;
}

function compileExprRK(ctx: Ctx, exp: Expression): number {
  if (!exp) {
    const tmp = allocTemp(ctx);
    regEmit(ctx.chunk, RegOp.LOADNIL, tmp, 0);
    return tmp;
  }
  switch (exp.type) {
    case "NilLiteral": {
      const tmp = allocTemp(ctx);
      regEmit(ctx.chunk, RegOp.LOADNIL, tmp, 0);
      return tmp;
    }
    case "BooleanLiteral": return constRK(ctx, exp.value);
    case "NumberLiteral":  return constRK(ctx, Number(exp.value));
    case "StringLiteral":  return constRK(ctx, exp.value);
    case "Identifier": {
      if (exp.name === "nil") {
        const tmp = allocTemp(ctx);
        regEmit(ctx.chunk, RegOp.LOADNIL, tmp, 0);
        return tmp;
      }
      if (exp.name === "true") return constRK(ctx, true);
      if (exp.name === "false") return constRK(ctx, false);
      const reg = ctx.locals.get(exp.name);
      if (reg !== undefined && reg < RK_OFFSET) return reg;
      return compileExpr(ctx, exp, -1);
    }
    default:
      return compileExpr(ctx, exp, -1);
  }
}

function compileCall(ctx: Ctx, exp: CallExpression, base: number, nResults: number): void {
  const c = ctx.chunk;
  const args = exp.args || [];
  const spread = hasSpread(args);

  reserveRegs(ctx, base, 1 + args.length + 1);
  compileExpr(ctx, exp.callee, base);

  for (let i = 0; i < args.length; i++) {
    if (i === args.length - 1 && spread) {
      if (isCallLike(args[i])) {
        compileCallMultiReg(ctx, args[i], base + 1 + i, 0);
      } else {
        regEmit(c, RegOp.VARARG, base + 1 + i, 0);
      }
    } else {
      compileExpr(ctx, args[i], base + 1 + i);
    }
  }

  const B = spread ? 0 : args.length + 1;
  regEmit(c, RegOp.CALL, base, B, nResults);
}

function compileMethodCall(ctx: Ctx, exp: MethodCallExpression, base: number, nResults: number): void {
  const c = ctx.chunk;
  const args = exp.args || [];
  const spread = hasSpread(args);

  reserveRegs(ctx, base, 2 + args.length + 1);

  const objReg = compileExpr(ctx, exp.object, -1);
  const methodRK = constRK(ctx, exp.method);
  regEmit(c, RegOp.SELF, base, objReg, methodRK);

  for (let i = 0; i < args.length; i++) {
    if (i === args.length - 1 && spread) {
      if (isCallLike(args[i])) {
        compileCallMultiReg(ctx, args[i], base + 2 + i, 0);
      } else {
        regEmit(c, RegOp.VARARG, base + 2 + i, 0);
      }
    } else {
      compileExpr(ctx, args[i], base + 2 + i);
    }
  }

  const B = spread ? 0 : args.length + 2;
  regEmit(c, RegOp.CALL, base, B, nResults);
}

function compileCallMultiReg(ctx: Ctx, exp: Expression, base: number, nResults: number): void {
  if (exp.type === "MethodCallExpression") {
    compileMethodCall(ctx, exp as MethodCallExpression, base, nResults);
  } else if (exp.type === "CallExpression") {
    compileCall(ctx, exp as CallExpression, base, nResults);
  }
}

function compileTailCall(ctx: Ctx, exp: Expression): void {
  const c = ctx.chunk;
  const base = ctx.freeReg;
  if (exp.type === "MethodCallExpression") {
    const args = exp.args || [];
    reserveRegs(ctx, base, 2 + args.length + 1);
    const objReg = compileExpr(ctx, exp.object, -1);
    regEmit(c, RegOp.SELF, base, objReg, constRK(ctx, exp.method));
    for (let i = 0; i < args.length; i++) compileExpr(ctx, args[i], base + 2 + i);
    regEmit(c, RegOp.TAILCALL, base, args.length + 2, 0);
  } else if (exp.type === "CallExpression") {
    const args = exp.args || [];
    reserveRegs(ctx, base, 1 + args.length + 1);
    compileExpr(ctx, exp.callee, base);
    for (let i = 0; i < args.length; i++) compileExpr(ctx, args[i], base + 1 + i);
    regEmit(c, RegOp.TAILCALL, base, args.length + 1, 0);
  }
}

function compileFunctionBody(
  ctx: Ctx,
  params: Param[],
  body: (Statement | LastStatement)[]
): number {
  const child = createCtx(ctx);
  let reg = 0;
  let nP = 0;
  let va = false;

  for (const p of params) {
    if (p.variadic) { va = true; continue; }
    child.locals.set(p.name, reg++);
    nP++;
  }

  child.nextReg = reg;
  child.freeReg = reg;
  child.isVararg = va;
  child.nParams = nP;
  child.chunk.nParams = nP;
  child.chunk.isVararg = va;
  child.chunk.maxRegs = reg;

  for (const stmt of body) compileStmt(child, stmt);

  const last = body.length > 0 ? body[body.length - 1] : null;
  if (!last || (last as any).type !== "ReturnStatement") {
    regEmit(child.chunk, RegOp.RETURN, 0, 1);
  }

  if (child.upvalueList.length > 0) {
    child.chunk.upvalues = child.upvalueList.map(uv => [uv.isLocal ? 1 : 0, uv.index]);
  }

  return regAddProto(ctx.chunk, child.chunk);
}

function compileStmt(ctx: Ctx, stmt: Statement | LastStatement): void {
  if (!stmt) return;
  const c = ctx.chunk;

  switch (stmt.type) {
    case "LocalStatement":
      compileLocalStmt(ctx, stmt);
      break;

    case "AssignmentStatement":
      compileAssignStmt(ctx, stmt);
      break;

    case "CompoundAssignmentStatement":
      compileCompoundAssign(ctx, stmt);
      break;

    case "FunctionCallStatement":
      compileFuncCallStmt(ctx, stmt);
      break;

    case "DoStatement": {
      const snap = pushScope(ctx);
      for (const s of stmt.body) compileStmt(ctx, s);
      if (ctx.nextReg > snap.nextReg) regEmit(c, RegOp.CLOSEUPVAL, snap.nextReg);
      popScope(ctx, snap);
      break;
    }

    case "WhileStatement":
      compileWhile(ctx, stmt);
      break;

    case "RepeatStatement":
      compileRepeat(ctx, stmt);
      break;

    case "IfStatement":
      compileIf(ctx, stmt);
      break;

    case "ForNumericStatement":
      compileForNumeric(ctx, stmt);
      break;

    case "ForInStatement":
      compileForIn(ctx, stmt);
      break;

    case "ReturnStatement":
      compileReturn(ctx, stmt);
      break;

    case "BreakStatement": {
      const lc = currentLoop(ctx);
      if (lc) {
        if (ctx.nextReg > lc.bodyRegStart) regEmit(c, RegOp.CLOSEUPVAL, lc.bodyRegStart);
        lc.breakPatches.push(emitJump(ctx));
      }
      break;
    }

    case "ContinueStatement": {
      const lc = currentLoop(ctx);
      if (lc) {
        if (ctx.nextReg > lc.bodyRegStart) regEmit(c, RegOp.CLOSEUPVAL, lc.bodyRegStart);
        lc.continuePatches.push(emitJump(ctx));
      }
      break;
    }

    case "LocalFunctionStatement": {
      const reg = allocLocal(ctx, stmt.name);
      const protoIdx = compileFunctionBody(ctx, stmt.params, stmt.body);
      regEmit(c, RegOp.CLOSURE, reg, protoIdx);
      break;
    }

    case "FunctionStatement":
      compileFuncStmt(ctx, stmt);
      break;

    case "TypeStatement":
    case "ExportTypeStatement":
    case "TypeFunctionStatement":
    case "ExportTypeFunctionStatement":
      break;

    default:
      break;
  }
}

function compileLocalStmt(ctx: Ctx, stmt: any): void {
  const c = ctx.chunk;
  const nVars = stmt.vars.length;

  if (stmt.values && stmt.values.length > 0) {
    const nVals = stmt.values.length;
    const lastVal = stmt.values[nVals - 1];
    const spread = nVals > 0 && (isCallLike(lastVal) || lastVal.type === "VarargExpression");

    const regs: number[] = [];
    for (let i = 0; i < nVars; i++) {
      const reg = ctx.nextReg++;
      if (ctx.freeReg < ctx.nextReg) ctx.freeReg = ctx.nextReg;
      ctx.chunk.maxRegs = Math.max(ctx.chunk.maxRegs, ctx.nextReg);
      regs.push(reg);
    }

    if (spread && nVars > nVals) {
      for (let i = 0; i < nVals - 1; i++) {
        compileExpr(ctx, stmt.values[i], regs[i]);
      }
      const extra = nVars - (nVals - 1);
      if (isCallLike(lastVal)) {
        compileCallMultiReg(ctx, lastVal, regs[nVals - 1], extra + 1);
      } else {
        regEmit(c, RegOp.VARARG, regs[nVals - 1], extra + 1);
      }
    } else {
      const count = Math.min(nVars, nVals);
      for (let i = 0; i < count; i++) {
        compileExpr(ctx, stmt.values[i], regs[i]);
      }

      if (nVals > nVars) {
        for (let i = nVars; i < nVals; i++) {
          const sv = saveFree(ctx);
          compileExpr(ctx, stmt.values[i], -1);
          restoreFree(ctx, sv);
        }
      }

      if (nVars > nVals) {
        regEmit(c, RegOp.LOADNIL, regs[nVals], nVars - nVals - 1);
      }
    }

    for (let i = 0; i < nVars; i++) {
      ctx.locals.set(stmt.vars[i].name, regs[i]);
    }
  } else {

    const regs: number[] = [];
    for (let i = 0; i < nVars; i++) {
      regs.push(allocLocal(ctx, stmt.vars[i].name));
    }
    regEmit(c, RegOp.LOADNIL, regs[0], nVars - 1);
  }
}

function compileAssignStmt(ctx: Ctx, stmt: any): void {
  const c = ctx.chunk;
  const nVars = stmt.vars.length;
  const nVals = stmt.values.length;
  const s = saveFree(ctx);

  const temps: number[] = [];
  const lastVal = nVals > 0 ? stmt.values[nVals - 1] : null;
  const spread = lastVal && (isCallLike(lastVal) || lastVal.type === "VarargExpression");

  if (spread && nVars > nVals) {
    for (let i = 0; i < nVals - 1; i++) {
      const t = allocTemp(ctx);
      compileExpr(ctx, stmt.values[i], t);
      temps.push(t);
    }
    const base = ctx.freeReg;
    const extra = nVars - (nVals - 1);
    if (isCallLike(lastVal!)) {
      compileCallMultiReg(ctx, lastVal!, base, extra + 1);
    } else {
      regEmit(c, RegOp.VARARG, base, extra + 1);
    }
    for (let i = 0; i < extra; i++) temps.push(base + i);
  } else {
    const count = Math.min(nVars, nVals);
    for (let i = 0; i < count; i++) {
      const t = allocTemp(ctx);
      compileExpr(ctx, stmt.values[i], t);
      temps.push(t);
    }

    for (let i = nVars; i < nVals; i++) {
      compileExpr(ctx, stmt.values[i], -1);
    }
  }

  for (let i = 0; i < nVars; i++) {
    const v = stmt.vars[i] as Var;
    const src = i < temps.length ? temps[i] : -1;
    assignToVar(ctx, v, src);
  }

  restoreFree(ctx, s);
}

function assignToIdent(ctx: Ctx, name: string, src: number): void {
  const c = ctx.chunk;
  const localReg = ctx.locals.get(name);
  if (localReg !== undefined) {
    if (src >= 0) {
      if (src !== localReg) regEmit(c, RegOp.MOVE, localReg, src);
    } else {
      regEmit(c, RegOp.LOADNIL, localReg, 0);
    }
    return;
  }
  const uv = resolveUpvalue(ctx, name);
  if (uv !== null) {
    if (src >= 0) {
      regEmit(c, RegOp.SETUPVAL, src, uv);
    } else {
      const tmp = allocTemp(ctx);
      regEmit(c, RegOp.LOADNIL, tmp, 0);
      regEmit(c, RegOp.SETUPVAL, tmp, uv);
    }
    return;
  }

  if (src >= 0) {
    regEmit(c, RegOp.SETGLOBAL, src, regAddConst(c, name));
  } else {
    const tmp = allocTemp(ctx);
    regEmit(c, RegOp.LOADNIL, tmp, 0);
    regEmit(c, RegOp.SETGLOBAL, tmp, regAddConst(c, name));
  }
}

function assignToVar(ctx: Ctx, v: Var, src: number): void {
  const c = ctx.chunk;
  if (v.type === "Identifier") {
    assignToIdent(ctx, v.name, src);
  } else if (v.type === "IndexExpression") {
    const obj = compileExpr(ctx, v.object, -1);
    const key = compileExprRK(ctx, v.index);
    if (src >= 0) {
      regEmit(c, RegOp.SETTABLE, obj, key, src);
    } else {
      const tmp = allocTemp(ctx);
      regEmit(c, RegOp.LOADNIL, tmp, 0);
      regEmit(c, RegOp.SETTABLE, obj, key, tmp);
    }
  } else if (v.type === "MemberExpression") {
    const obj = compileExpr(ctx, v.object, -1);
    const key = constRK(ctx, v.property);
    if (src >= 0) {
      regEmit(c, RegOp.SETTABLE, obj, key, src);
    } else {
      const tmp = allocTemp(ctx);
      regEmit(c, RegOp.LOADNIL, tmp, 0);
      regEmit(c, RegOp.SETTABLE, obj, key, tmp);
    }
  }
}

function compileCompoundAssign(ctx: Ctx, stmt: any): void {
  const c = ctx.chunk;
  const s = saveFree(ctx);
  const baseOp = stmt.operator.replace("=", "");
  const arithOps: Record<string, RegOp> = {
    "+": RegOp.ADD, "-": RegOp.SUB, "*": RegOp.MUL, "/": RegOp.DIV,
    "%": RegOp.MOD, "^": RegOp.POW, "//": RegOp.IDIV,
  };
  const op = arithOps[baseOp];
  const isConcat = baseOp === "..";

  if (stmt.var.type === "Identifier") {
    const localReg = ctx.locals.get(stmt.var.name);
    if (localReg !== undefined) {
      if (isConcat) {

        const concatBase = ctx.freeReg;
        reserveRegs(ctx, concatBase, 2);
        regEmit(c, RegOp.MOVE, concatBase, localReg);
        compileExpr(ctx, stmt.value, concatBase + 1);
        regEmit(c, RegOp.CONCAT, localReg, concatBase, concatBase + 1);
      } else if (op !== undefined) {
        const valRK = compileExprRK(ctx, stmt.value);
        regEmit(c, op, localReg, localReg, valRK);
      }
    } else {
      const uv = resolveUpvalue(ctx, stmt.var.name);
      const tmp = allocTemp(ctx);
      if (uv !== null) {
        regEmit(c, RegOp.GETUPVAL, tmp, uv);
      } else {
        regEmit(c, RegOp.GETGLOBAL, tmp, regAddConst(c, stmt.var.name));
      }
      if (isConcat) {
        const valReg = allocTemp(ctx);
        compileExpr(ctx, stmt.value, valReg);
        regEmit(c, RegOp.CONCAT, tmp, tmp, valReg);
      } else if (op !== undefined) {
        const valRK = compileExprRK(ctx, stmt.value);
        regEmit(c, op, tmp, tmp, valRK);
      }
      if (uv !== null) {
        regEmit(c, RegOp.SETUPVAL, tmp, uv);
      } else {
        regEmit(c, RegOp.SETGLOBAL, tmp, regAddConst(c, stmt.var.name));
      }
    }
  } else {

    const objReg = compileExpr(ctx, (stmt.var as any).object, -1);
    let keyRK: number;
    if (stmt.var.type === "IndexExpression") {
      keyRK = compileExprRK(ctx, (stmt.var as any).index);
    } else {
      keyRK = constRK(ctx, (stmt.var as any).property);
    }
    const oldReg = allocTemp(ctx);
    regEmit(c, RegOp.GETTABLE, oldReg, objReg, keyRK);
    if (isConcat) {
      const valReg = allocTemp(ctx);
      compileExpr(ctx, stmt.value, valReg);
      regEmit(c, RegOp.CONCAT, oldReg, oldReg, valReg);
    } else if (op !== undefined) {
      const valRK = compileExprRK(ctx, stmt.value);
      regEmit(c, op, oldReg, oldReg, valRK);
    }
    regEmit(c, RegOp.SETTABLE, objReg, keyRK, oldReg);
  }

  restoreFree(ctx, s);
}

function compileFuncCallStmt(ctx: Ctx, stmt: any): void {
  const s = saveFree(ctx);
  const call = stmt.call;
  const base = ctx.freeReg;
  if (call.type === "MethodCallExpression" || (call.object && call.method)) {
    compileMethodCall(ctx, call, base, 1);
  } else {
    compileCall(ctx, call, base, 1);
  }
  restoreFree(ctx, s);
}

function compileWhile(ctx: Ctx, stmt: any): void {
  const c = ctx.chunk;
  const condPC = regPC(c);
  const snap = pushScope(ctx);
  const bodyStart = ctx.nextReg;
  pushLoop(ctx, bodyStart);

  const sv = saveFree(ctx);
  const cond = compileExpr(ctx, stmt.condition, -1);
  regEmit(c, RegOp.TEST, cond, 0, 0);
  const jmpOut = emitJump(ctx);
  restoreFree(ctx, sv);

  for (const st of stmt.body) compileStmt(ctx, st);

  resolveContinues(ctx);
  if (ctx.nextReg > bodyStart) regEmit(c, RegOp.CLOSEUPVAL, bodyStart);

  const back = emitJump(ctx);
  patchJump(ctx, back, condPC);
  patchJump(ctx, jmpOut, regPC(c));

  popLoop(ctx);
  popScope(ctx, snap);
}

function compileRepeat(ctx: Ctx, stmt: any): void {
  const c = ctx.chunk;
  const bodyPC = regPC(c);
  const snap = pushScope(ctx);
  const bodyStart = ctx.nextReg;
  pushLoop(ctx, bodyStart);

  for (const st of stmt.body) compileStmt(ctx, st);

  resolveContinues(ctx);
  if (ctx.nextReg > bodyStart) regEmit(c, RegOp.CLOSEUPVAL, bodyStart);

  const sv = saveFree(ctx);
  const cond = compileExpr(ctx, stmt.condition, -1);
  regEmit(c, RegOp.TEST, cond, 0, 0);
  const jmpBack = emitJump(ctx);
  patchJump(ctx, jmpBack, bodyPC);
  restoreFree(ctx, sv);

  popLoop(ctx);
  popScope(ctx, snap);
}

function compileIf(ctx: Ctx, stmt: any): void {
  const c = ctx.chunk;
  const endJumps: number[] = [];

  let sv = saveFree(ctx);
  const cond = compileExpr(ctx, stmt.condition, -1);
  regEmit(c, RegOp.TEST, cond, 0, 0);
  const jmpElse = emitJump(ctx);
  restoreFree(ctx, sv);

  let snap = pushScope(ctx);
  for (const st of stmt.thenBody) compileStmt(ctx, st);
  if (ctx.nextReg > snap.nextReg) regEmit(c, RegOp.CLOSEUPVAL, snap.nextReg);
  popScope(ctx, snap);
  endJumps.push(emitJump(ctx));
  patchJump(ctx, jmpElse, regPC(c));

  for (const ec of stmt.elseifClauses) {
    sv = saveFree(ctx);
    const cr = compileExpr(ctx, ec.condition, -1);
    regEmit(c, RegOp.TEST, cr, 0, 0);
    const jmpNext = emitJump(ctx);
    restoreFree(ctx, sv);

    snap = pushScope(ctx);
    for (const st of ec.body) compileStmt(ctx, st);
    if (ctx.nextReg > snap.nextReg) regEmit(c, RegOp.CLOSEUPVAL, snap.nextReg);
    popScope(ctx, snap);
    endJumps.push(emitJump(ctx));
    patchJump(ctx, jmpNext, regPC(c));
  }

  if (stmt.elseBody) {
    snap = pushScope(ctx);
    for (const st of stmt.elseBody) compileStmt(ctx, st);
    if (ctx.nextReg > snap.nextReg) regEmit(c, RegOp.CLOSEUPVAL, snap.nextReg);
    popScope(ctx, snap);
  }

  const end = regPC(c);
  for (const j of endJumps) patchJump(ctx, j, end);
}

function compileForNumeric(ctx: Ctx, stmt: any): void {
  const c = ctx.chunk;
  const snap = pushScope(ctx);
  const sv = saveFree(ctx);

  const counterReg = allocHidden(ctx, "for_i");
  const limitReg   = allocHidden(ctx, "for_lim");
  const stepReg    = allocHidden(ctx, "for_step");
  const userReg    = allocLocal(ctx, stmt.var.name);

  compileExpr(ctx, stmt.start, counterReg);
  compileExpr(ctx, stmt.end, limitReg);
  if (stmt.step) {
    compileExpr(ctx, stmt.step, stepReg);
  } else {
    regEmit(c, RegOp.LOADK, stepReg, regAddConst(c, 1));
  }

  const forprepPC = regPC(c);
  regEmit(c, RegOp.FORPREP, counterReg, 0);

  const bodyStart = ctx.nextReg;
  pushLoop(ctx, bodyStart);

  for (const st of stmt.body) compileStmt(ctx, st);
  resolveContinues(ctx);
  regEmit(c, RegOp.CLOSEUPVAL, userReg);

  const forloopPC = regPC(c);
  const bodyStartPC = forprepPC + 1;
  regEmit(c, RegOp.FORLOOP, counterReg, bodyStartPC - forloopPC - 1);
  regPatch(c, forprepPC * 4, 'B', forloopPC - forprepPC - 1);

  popLoop(ctx);
  restoreFree(ctx, sv);
  popScope(ctx, snap);
}

function compileForIn(ctx: Ctx, stmt: any): void {
  const c = ctx.chunk;
  const snap = pushScope(ctx);
  const sv = saveFree(ctx);

  const iterReg  = allocHidden(ctx, "for_iter");
  const stateReg = allocHidden(ctx, "for_state");
  const ctrlReg  = allocHidden(ctx, "for_ctrl");

  const iterCount = stmt.iter.length;
  if (iterCount === 1 && isCallLike(stmt.iter[0])) {
    compileCallMultiReg(ctx, stmt.iter[0], iterReg, 4);
  } else if (iterCount > 1 && isCallLike(stmt.iter[iterCount - 1])) {
    for (let i = 0; i < iterCount - 1; i++) {
      compileExpr(ctx, stmt.iter[i], iterReg + i);
    }
    const remaining = 3 - (iterCount - 1);
    compileCallMultiReg(ctx, stmt.iter[iterCount - 1], iterReg + iterCount - 1, remaining + 1);
  } else {
    for (let i = 0; i < Math.min(iterCount, 3); i++) {
      compileExpr(ctx, stmt.iter[i], iterReg + i);
    }
    for (let i = iterCount; i < 3; i++) {
      regEmit(c, RegOp.LOADNIL, iterReg + i, 0);
    }
  }

  regEmit(c, RegOp.ITERPREP, iterReg);

  const nVars = stmt.vars.length;
  for (const v of stmt.vars) allocLocal(ctx, v.name);

  const loopTopPC = regPC(c);
  const bodyStart = ctx.nextReg;
  pushLoop(ctx, bodyStart);

  regEmit(c, RegOp.TFORLOOP, iterReg, 0, nVars);
  const jmpEnd = emitJump(ctx);

  for (const st of stmt.body) compileStmt(ctx, st);

  resolveContinues(ctx);
  regEmit(c, RegOp.CLOSEUPVAL, iterReg + 3);

  const back = emitJump(ctx);
  patchJump(ctx, back, loopTopPC);
  patchJump(ctx, jmpEnd, regPC(c));

  popLoop(ctx);
  restoreFree(ctx, sv);
  popScope(ctx, snap);
}

function compileReturn(ctx: Ctx, stmt: any): void {
  const c = ctx.chunk;
  if (!stmt.values || stmt.values.length === 0) {
    regEmit(c, RegOp.RETURN, 0, 1);
    return;
  }

  const nVals = stmt.values.length;
  const lastVal = stmt.values[nVals - 1];
  const spread = isCallLike(lastVal) || lastVal.type === "VarargExpression";

  if (nVals === 1 && isCallLike(lastVal) && !hasSpread((lastVal as any).args)) {
    compileTailCall(ctx, lastVal);
  } else if (nVals === 1 && isCallLike(lastVal)) {
    const base = ctx.freeReg;
    compileCallMultiReg(ctx, lastVal, base, 0);
    regEmit(c, RegOp.RETURN, base, 0);
  } else if (nVals === 1 && lastVal.type === "VarargExpression") {
    const base = ctx.freeReg;
    regEmit(c, RegOp.VARARG, base, 0);
    regEmit(c, RegOp.RETURN, base, 0);
  } else if (spread) {
    const base = ctx.freeReg;
    reserveRegs(ctx, base, nVals);
    for (let i = 0; i < nVals - 1; i++) {
      compileExpr(ctx, stmt.values[i], base + i);
    }
    if (isCallLike(lastVal)) {
      compileCallMultiReg(ctx, lastVal, base + nVals - 1, 0);
    } else {
      regEmit(c, RegOp.VARARG, base + nVals - 1, 0);
    }
    regEmit(c, RegOp.RETURN, base, 0);
  } else {
    const base = ctx.freeReg;
    reserveRegs(ctx, base, nVals);
    for (let i = 0; i < nVals; i++) {
      compileExpr(ctx, stmt.values[i], base + i);
    }
    regEmit(c, RegOp.RETURN, base, nVals + 1);
  }
}

function compileFuncStmt(ctx: Ctx, stmt: any): void {
  const c = ctx.chunk;
  const s = saveFree(ctx);
  const fn = stmt.name as FuncName;
  const params: Param[] = fn.method
    ? [{ type: "Param", name: "self", loc: stmt.loc } as Param, ...stmt.params]
    : stmt.params;
  const protoIdx = compileFunctionBody(ctx, params, stmt.body);

  if (fn.method) {
    const obj = compileExpr(ctx, fn.base, -1);
    const closure = allocTemp(ctx);
    regEmit(c, RegOp.CLOSURE, closure, protoIdx);
    const key = constRK(ctx, fn.method);
    regEmit(c, RegOp.SETTABLE, obj, key, closure);
  } else if (fn.base.type === "Identifier") {
    const localReg = ctx.locals.get(fn.base.name);
    if (localReg !== undefined) {
      regEmit(c, RegOp.CLOSURE, localReg, protoIdx);
    } else {
      const tmp = allocTemp(ctx);
      regEmit(c, RegOp.CLOSURE, tmp, protoIdx);
      const uv = resolveUpvalue(ctx, fn.base.name);
      if (uv !== null) {
        regEmit(c, RegOp.SETUPVAL, tmp, uv);
      } else {
        regEmit(c, RegOp.SETGLOBAL, tmp, regAddConst(c, fn.base.name));
      }
    }
  } else if (fn.base.type === "MemberExpression") {
    const obj = compileExpr(ctx, (fn.base as MemberExpression).object, -1);
    const closure = allocTemp(ctx);
    regEmit(c, RegOp.CLOSURE, closure, protoIdx);
    const key = constRK(ctx, (fn.base as MemberExpression).property);
    regEmit(c, RegOp.SETTABLE, obj, key, closure);
  }

  restoreFree(ctx, s);
}

export function regCompile(ast: Chunk): RegBytecodeChunk {
  const ctx = createCtx();
  ctx.chunk.isVararg = true;
  for (const stmt of ast.body) compileStmt(ctx, stmt);

  const last = ast.body.length > 0 ? ast.body[ast.body.length - 1] : null;
  if (!last || (last as any).type !== "ReturnStatement") {
    regEmit(ctx.chunk, RegOp.RETURN, 0, 1);
  }

  return ctx.chunk;
}
