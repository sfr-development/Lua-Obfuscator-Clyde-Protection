import type {
  Chunk,
  Statement,
  LastStatement,
  Expression,
  Var,
} from "../ast/types.js";
import type { BytecodeChunk, Constant } from "./bytecode.js";
import { Op, emit, addConst } from "./bytecode.js";

interface LoopContext {
  breakPatches: number[];
  continuePatches: number[];
}

interface UpvalueRef {
  name: string;
  isLocal: boolean;
  index: number;
}

interface CompileContext {
  chunk: BytecodeChunk;
  locals: Map<string, number>;
  nextSlot: number;
  loopStack: LoopContext[];
  parentCtx?: CompileContext;
  upvalues: Map<string, number>;
  upvalueList: UpvalueRef[];
  hasVarargs: boolean;
  nParams: number;
  uniqueCounter: number;
}

function createContext(parentCtx?: CompileContext): CompileContext {
  return {
    chunk: { K: [], code: [] },
    locals: new Map(),
    nextSlot: 0,
    loopStack: [],
    parentCtx,
    upvalues: new Map(),
    upvalueList: [],
    hasVarargs: false,
    nParams: 0,
    uniqueCounter: 0,
  };
}

function allocFreshLocal(ctx: CompileContext, baseName: string): number {
  const name = `\0${baseName}_${ctx.uniqueCounter++}`;
  const slot = ctx.nextSlot++;
  ctx.locals.set(name, slot);
  return slot;
}

function addProto(parentCtx: CompileContext, proto: BytecodeChunk): number {
  const target = parentCtx.chunk;
  if (!target.protos) target.protos = [];
  target.protos.push(proto);
  return target.protos.length;
}

function resolveUpvalue(ctx: CompileContext, name: string): number | null {
  const existing = ctx.upvalues.get(name);
  if (existing !== undefined) return existing;
  if (!ctx.parentCtx) return null;
  const parent = ctx.parentCtx;
  const localSlot = parent.locals.get(name);
  if (localSlot !== undefined) {
    const idx = ctx.upvalueList.length;
    ctx.upvalueList.push({ name, isLocal: true, index: localSlot });
    ctx.upvalues.set(name, idx);
    return idx;
  }
  const parentUpval = resolveUpvalue(parent, name);
  if (parentUpval !== null) {
    const idx = ctx.upvalueList.length;
    ctx.upvalueList.push({ name, isLocal: false, index: parentUpval });
    ctx.upvalues.set(name, idx);
    return idx;
  }
  return null;
}

function allocLocal(ctx: CompileContext, name: string): number {
  let slot = ctx.locals.get(name);
  if (slot === undefined) {
    slot = ctx.nextSlot++;
    ctx.locals.set(name, slot);
  }
  return slot;
}

function pushScope(ctx: CompileContext): Map<string, number> {
  return new Map(ctx.locals);
}

function popScope(ctx: CompileContext, prev: Map<string, number>): void {
  ctx.locals = prev;
}

function pushLoop(ctx: CompileContext): LoopContext {
  const loop: LoopContext = { breakPatches: [], continuePatches: [] };
  ctx.loopStack.push(loop);
  return loop;
}

function popLoop(ctx: CompileContext): void {
  const loop = ctx.loopStack.pop();
  if (loop) {
    const end = ctx.chunk.code.length;
    for (const idx of loop.breakPatches) ctx.chunk.code[idx] = end;

    for (const idx of loop.continuePatches) ctx.chunk.code[idx] = end;
  }
}

function resolveContinues(ctx: CompileContext): void {
  const loop = ctx.loopStack[ctx.loopStack.length - 1];
  if (loop) {
    const target = ctx.chunk.code.length;
    for (const idx of loop.continuePatches) ctx.chunk.code[idx] = target;
    loop.continuePatches = [];
  }
}

function currentLoop(ctx: CompileContext): LoopContext | undefined {
  return ctx.loopStack[ctx.loopStack.length - 1];
}

function isCallLike(exp: Expression): boolean {
  return exp.type === "CallExpression" || exp.type === "MethodCallExpression";
}

function hasSpreadArg(args: Expression[]): boolean {
  if (args.length === 0) return false;
  const last = args[args.length - 1];
  return isCallLike(last) || last.type === "VarargExpression";
}

function compileSpreadLastArg(ctx: CompileContext, lastArg: Expression): void {
  if (isCallLike(lastArg)) {
    compileCallMulti(ctx, lastArg, -1);
  } else {

    emit(ctx.chunk, Op.LOAD_VARARG, -1);
  }
}

function compileCallMulti(ctx: CompileContext, exp: Expression, nResults: number): void {
  const c = ctx.chunk;
  if (exp.type === "MethodCallExpression") {
    const spread = hasSpreadArg(exp.args);
    if (spread) {
      emit(c, Op.MARK);
      compileExpression(ctx, exp.object);
      emit(c, Op.DUP);
      emit(c, Op.PUSH_K, addConst(c, exp.method));
      emit(c, Op.GET_TABLE);
      emit(c, Op.SWAP);
      for (let i = 0; i < exp.args.length - 1; i++) compileExpression(ctx, exp.args[i]);
      compileSpreadLastArg(ctx, exp.args[exp.args.length - 1]);
      emit(c, Op.CALL_DYNAMIC, nResults);
    } else {
      compileExpression(ctx, exp.object);
      emit(c, Op.DUP);
      emit(c, Op.PUSH_K, addConst(c, exp.method));
      emit(c, Op.GET_TABLE);
      emit(c, Op.SWAP);
      for (const a of exp.args) compileExpression(ctx, a);
      emit(c, Op.CALL_MULTI, exp.args.length + 1, nResults);
    }
  } else if (exp.type === "CallExpression") {
    const spread = hasSpreadArg(exp.args);
    if (spread) {
      emit(c, Op.MARK);
      compileExpression(ctx, exp.callee);
      for (let i = 0; i < exp.args.length - 1; i++) compileExpression(ctx, exp.args[i]);
      compileSpreadLastArg(ctx, exp.args[exp.args.length - 1]);
      emit(c, Op.CALL_DYNAMIC, nResults);
    } else {
      compileExpression(ctx, exp.callee);
      for (const a of exp.args) compileExpression(ctx, a);
      emit(c, Op.CALL_MULTI, exp.args.length, nResults);
    }
  }
}

function compileTailCall(ctx: CompileContext, exp: Expression): void {
  const c = ctx.chunk;
  if (exp.type === "MethodCallExpression") {
    compileExpression(ctx, exp.object);
    emit(c, Op.DUP);
    emit(c, Op.PUSH_K, addConst(c, exp.method)); emit(c, Op.GET_TABLE);
    emit(c, Op.SWAP);
    for (const a of exp.args) compileExpression(ctx, a);
    emit(c, Op.TAILCALL, exp.args.length + 1);
  } else if (exp.type === "CallExpression") {
    compileExpression(ctx, exp.callee);
    for (const a of exp.args) compileExpression(ctx, a);
    emit(c, Op.TAILCALL, exp.args.length);
  }
}

function compileFunctionBody(
  ctx: CompileContext,
  params: { name: string; variadic?: boolean }[],
  body: (Statement | LastStatement)[]
): number {
  const protoCtx = createContext(ctx);
  protoCtx.chunk = { K: [], code: [] };
  let slot = 0;
  let nParams = 0;
  let hasVarargs = false;

  for (const p of params) {
    if (p.variadic) {
      hasVarargs = true;
      continue;
    }
    protoCtx.locals.set(p.name, slot++);
    nParams++;
  }

  protoCtx.nextSlot = slot;
  protoCtx.hasVarargs = hasVarargs;
  protoCtx.nParams = nParams;

  for (const stmt of body) compileStatement(protoCtx, stmt);

  const lastStmt = body.length > 0 ? body[body.length - 1] : null;
  if (!lastStmt || (lastStmt as any).type !== "ReturnStatement") {
    emit(protoCtx.chunk, Op.RETURN, 0);
  }

  if (protoCtx.upvalueList.length > 0) {
    protoCtx.chunk.upvalues = protoCtx.upvalueList.map(uv => [
      uv.isLocal ? 1 : 0,
      uv.index
    ]);
  }

  (protoCtx.chunk as any).nParams = nParams;
  (protoCtx.chunk as any).hasVarargs = hasVarargs;

  return addProto(ctx, protoCtx.chunk);
}

function compileExpression(ctx: CompileContext, exp: Expression): void {
  if (!exp) {
    emit(ctx.chunk, Op.PUSH_NIL);
    return;
  }
  const c = ctx.chunk;
  switch (exp.type) {
    case "NilLiteral":
      emit(c, Op.PUSH_NIL);
      break;
    case "BooleanLiteral":
      emit(c, exp.value ? Op.PUSH_TRUE : Op.PUSH_FALSE);
      break;
    case "NumberLiteral": {
      const n = Number(exp.value);
      emit(c, Op.PUSH_K, addConst(c, n));
      break;
    }
    case "StringLiteral":
      emit(c, Op.PUSH_K, addConst(c, exp.value));
      break;
    case "Identifier": {
      if (exp.name === "nil") { emit(c, Op.PUSH_NIL); break; }
      if (exp.name === "true") { emit(c, Op.PUSH_TRUE); break; }
      if (exp.name === "false") { emit(c, Op.PUSH_FALSE); break; }
      const slot = ctx.locals.get(exp.name);
      if (slot !== undefined) {
        emit(c, Op.LOAD_L, slot);
      } else {
        const upvalIdx = resolveUpvalue(ctx, exp.name);
        if (upvalIdx !== null) {
          emit(c, Op.LOAD_UPVAL, upvalIdx);
        } else {
          emit(c, Op.LOAD_G, addConst(c, exp.name));
        }
      }
      break;
    }
    case "BinaryExpression": {

      if (exp.operator === "and") {
        compileExpression(ctx, exp.left);
        emit(c, Op.DUP);
        const jmpFalse = c.code.length;
        emit(c, Op.JMP_F, 0);
        emit(c, Op.POP, 1);
        compileExpression(ctx, exp.right);
        c.code[jmpFalse + 1] = c.code.length;
        break;
      }

      if (exp.operator === "or") {
        compileExpression(ctx, exp.left);
        emit(c, Op.DUP);
        emit(c, Op.NOT);
        const jmpTrue = c.code.length;
        emit(c, Op.JMP_F, 0);
        emit(c, Op.POP, 1);
        compileExpression(ctx, exp.right);
        c.code[jmpTrue + 1] = c.code.length;
        break;
      }
      compileExpression(ctx, exp.left);
      compileExpression(ctx, exp.right);
      const opMap: Record<string, Op> = {
        "+": Op.ADD, "-": Op.SUB, "*": Op.MUL, "/": Op.DIV,
        "%": Op.MOD, "^": Op.POW, "..": Op.CONCAT,
        "//": Op.IDIV,
        "==": Op.EQ, "~=": Op.NE, "<": Op.LT, "<=": Op.LE,
        ">": Op.GT, ">=": Op.GE,
      };
      const op = opMap[exp.operator];
      if (op !== undefined) emit(c, op);
      break;
    }
    case "UnaryExpression": {
      compileExpression(ctx, exp.argument);
      if (exp.operator === "not") emit(c, Op.NOT);
      else if (exp.operator === "-") emit(c, Op.UNM);
      else if (exp.operator === "#") emit(c, Op.LEN);
      break;
    }
    case "ParenExpression":
      compileExpression(ctx, exp.expression);
      break;
    case "CallExpression": {
      if (hasSpreadArg(exp.args)) {
        emit(c, Op.MARK);
        compileExpression(ctx, exp.callee);
        for (let i = 0; i < exp.args.length - 1; i++) compileExpression(ctx, exp.args[i]);
        compileSpreadLastArg(ctx, exp.args[exp.args.length - 1]);
        emit(c, Op.CALL_DYNAMIC, 1);
      } else {
        compileExpression(ctx, exp.callee);
        for (const a of exp.args) compileExpression(ctx, a);
        emit(c, Op.CALL, exp.args.length);
      }
      break;
    }
    case "MethodCallExpression": {
      if (hasSpreadArg(exp.args)) {
        emit(c, Op.MARK);
        compileExpression(ctx, exp.object);
        emit(c, Op.DUP);
        emit(c, Op.PUSH_K, addConst(c, exp.method));
        emit(c, Op.GET_TABLE);
        emit(c, Op.SWAP);
        for (let i = 0; i < exp.args.length - 1; i++) compileExpression(ctx, exp.args[i]);
        compileSpreadLastArg(ctx, exp.args[exp.args.length - 1]);
        emit(c, Op.CALL_DYNAMIC, 1);
      } else {
        compileExpression(ctx, exp.object);
        emit(c, Op.DUP);
        const idx = addConst(c, exp.method);
        emit(c, Op.PUSH_K, idx);
        emit(c, Op.GET_TABLE);
        emit(c, Op.SWAP);
        for (const a of exp.args) compileExpression(ctx, a);
        emit(c, Op.CALL, exp.args.length + 1);
      }
      break;
    }
    case "IndexExpression":
      compileExpression(ctx, exp.object);
      compileExpression(ctx, exp.index);
      emit(c, Op.GET_TABLE);
      break;
    case "MemberExpression":
      compileExpression(ctx, exp.object);
      emit(c, Op.PUSH_K, addConst(c, exp.property));
      emit(c, Op.GET_TABLE);
      break;
    case "TableConstructor": {
      emit(c, Op.NEW_TABLE);
      let arrIdx = 0;
      const fields = exp.fields;
      for (let fi = 0; fi < fields.length; fi++) {
        const f = fields[fi];
        const isLast = fi === fields.length - 1;

        if (f.kind === "index") {
          emit(c, Op.DUP);
          compileExpression(ctx, f.index);
          compileExpression(ctx, f.value);
          emit(c, Op.SET_TABLE);
        } else if (f.kind === "named") {
          emit(c, Op.DUP);
          emit(c, Op.PUSH_K, addConst(c, f.name));
          compileExpression(ctx, f.value);
          emit(c, Op.SET_TABLE);
        } else {

          arrIdx++;
          if (isLast && (isCallLike(f.value) || f.value.type === "VarargExpression")) {

            emit(c, Op.MARK);
            if (isCallLike(f.value)) {
              compileCallMulti(ctx, f.value, -1);
            } else {
              emit(c, Op.LOAD_VARARG, -1);
            }
            emit(c, Op.SETLIST, arrIdx);
          } else {
            emit(c, Op.DUP);
            emit(c, Op.PUSH_K, addConst(c, arrIdx));
            compileExpression(ctx, f.value);
            emit(c, Op.SET_TABLE);
          }
        }
      }
      break;
    }
    case "TypeAssertion":
      compileExpression(ctx, exp.expression);
      break;
    case "VarargExpression":
      emit(c, Op.LOAD_VARARG, 1);
      break;
    case "StringInterpolation": {
      if (exp.parts.length === 0) {
        emit(c, Op.PUSH_K, addConst(c, ""));
      } else {
        let first = true;
        for (const p of exp.parts) {
          if (typeof p === "string") {
            emit(c, Op.PUSH_K, addConst(c, p));
          } else {
            compileExpression(ctx, p);
          }
          if (!first) emit(c, Op.CONCAT);
          first = false;
        }
      }
      break;
    }
    case "FunctionExpression": {
      const proto = compileFunctionBody(ctx, exp.params, exp.body);
      emit(c, Op.CLOSURE, proto);
      break;
    }
    case "IfElseExpression": {
      const endJumps: number[] = [];

      compileExpression(ctx, exp.condition);
      const jmpElse = c.code.length;
      emit(c, Op.JMP_F, 0);
      compileExpression(ctx, exp.thenExp);
      endJumps.push(c.code.length + 1);
      emit(c, Op.JMP, 0);
      c.code[jmpElse + 1] = c.code.length;

      if (exp.elseifClauses) {
        for (const clause of exp.elseifClauses) {
          compileExpression(ctx, clause.condition);
          const jmpNext = c.code.length;
          emit(c, Op.JMP_F, 0);
          compileExpression(ctx, clause.value);
          endJumps.push(c.code.length + 1);
          emit(c, Op.JMP, 0);
          c.code[jmpNext + 1] = c.code.length;
        }
      }

      compileExpression(ctx, exp.elseExp);
      const end = c.code.length;
      for (const pos of endJumps) c.code[pos] = end;
      break;
    }
    default:
      emit(c, Op.PUSH_NIL);
  }
}

function compileStatement(ctx: CompileContext, stmt: Statement | LastStatement): void {
  if (!stmt) return;
  const c = ctx.chunk;
  switch (stmt.type) {
    case "LocalStatement": {
      const nVars = stmt.vars.length;

      if (stmt.values && stmt.values.length > 0) {
        const nVals = stmt.values.length;
        const lastVal = stmt.values[nVals - 1];
        const extraNeeded = nVars - nVals;

        if (nVals === 1 && extraNeeded > 0 && isCallLike(lastVal)) {
          compileCallMulti(ctx, lastVal, nVars);
        } else if (nVals > 1 && extraNeeded > 0 && isCallLike(lastVal)) {
          for (let i = 0; i < nVals - 1; i++) compileExpression(ctx, stmt.values[i]);
          compileCallMulti(ctx, lastVal, extraNeeded + 1);
        } else if (nVals === 1 && extraNeeded > 0 && lastVal.type === "VarargExpression") {
          emit(c, Op.LOAD_VARARG, nVars);
        } else if (nVals > 1 && extraNeeded > 0 && lastVal.type === "VarargExpression") {
          for (let i = 0; i < nVals - 1; i++) compileExpression(ctx, stmt.values[i]);
          emit(c, Op.LOAD_VARARG, extraNeeded + 1);
        } else {
          for (const val of stmt.values) compileExpression(ctx, val);
          if (nVals > nVars) {
            emit(c, Op.POP, nVals - nVars);
          }
          for (let i = 0; i < nVars - nVals; i++) {
            emit(c, Op.PUSH_NIL);
          }
        }

        for (const v of stmt.vars) allocLocal(ctx, v.name);
        for (let i = nVars - 1; i >= 0; i--) {
          emit(c, Op.STORE_L, ctx.locals.get(stmt.vars[i].name)!);
        }
      } else {

        for (const v of stmt.vars) {
          allocLocal(ctx, v.name);
          emit(c, Op.PUSH_NIL);
          emit(c, Op.STORE_L, ctx.locals.get(v.name)!);
        }
      }
      break;
    }

    case "AssignmentStatement": {
      const nVars = stmt.vars.length;
      const nVals = stmt.values.length;

      const allSimple = stmt.vars.every(v => v.type === "Identifier");

      if (allSimple && nVals > 0 && nVars >= nVals) {
        const lastVal = stmt.values[nVals - 1];
        const extraNeeded = nVars - nVals;

        if (nVals === 1 && isCallLike(lastVal)) {

          compileCallMulti(ctx, lastVal, nVars);
        } else if (nVals > 1 && isCallLike(lastVal)) {

          for (let i = 0; i < nVals - 1; i++) compileExpression(ctx, stmt.values[i]);
          compileCallMulti(ctx, lastVal, extraNeeded + 1);
        } else if (nVals === 1 && lastVal.type === "VarargExpression") {

          emit(c, Op.LOAD_VARARG, nVars);
        } else if (nVals > 1 && lastVal.type === "VarargExpression") {

          for (let i = 0; i < nVals - 1; i++) compileExpression(ctx, stmt.values[i]);
          emit(c, Op.LOAD_VARARG, extraNeeded + 1);
        } else {

          for (const val of stmt.values) compileExpression(ctx, val);
          for (let i = 0; i < extraNeeded; i++) emit(c, Op.PUSH_NIL);
        }

        for (let i = nVars - 1; i >= 0; i--) {
          const v = stmt.vars[i] as { type: "Identifier"; name: string };
          const slot = ctx.locals.get(v.name);
          if (slot !== undefined) {
            emit(c, Op.STORE_L, slot);
          } else {
            const upvalIdx = resolveUpvalue(ctx, v.name);
            if (upvalIdx !== null) {
              emit(c, Op.STORE_UPVAL, upvalIdx);
            } else {
              emit(c, Op.STORE_G, addConst(c, v.name));
            }
          }
        }
      } else {

        const n = Math.min(nVars, nVals);
        for (let i = 0; i < n; i++) {
          const v = stmt.vars[i];
          const val = stmt.values[i];
          if (v.type === "Identifier") {
            compileExpression(ctx, val);
            const slot = ctx.locals.get(v.name);
            if (slot !== undefined) {
              emit(c, Op.STORE_L, slot);
            } else {
              const upvalIdx = resolveUpvalue(ctx, v.name);
              if (upvalIdx !== null) {
                emit(c, Op.STORE_UPVAL, upvalIdx);
              } else {
                emit(c, Op.STORE_G, addConst(c, v.name));
              }
            }
          } else {

            if (v.type === "IndexExpression") {
              compileExpression(ctx, v.object);
              compileExpression(ctx, v.index);
            } else if (v.type === "MemberExpression") {
              compileExpression(ctx, v.object);
              emit(c, Op.PUSH_K, addConst(c, v.property));
            }
            compileExpression(ctx, val);
            emit(c, Op.SET_TABLE);
          }
        }

        for (let i = n; i < nVars; i++) {
          const v = stmt.vars[i];
          if (v.type === "Identifier") {
            emit(c, Op.PUSH_NIL);
            const slot = ctx.locals.get(v.name);
            if (slot !== undefined) {
              emit(c, Op.STORE_L, slot);
            } else {
              const upvalIdx = resolveUpvalue(ctx, v.name);
              if (upvalIdx !== null) {
                emit(c, Op.STORE_UPVAL, upvalIdx);
              } else {
                emit(c, Op.STORE_G, addConst(c, v.name));
              }
            }
          }
        }

        for (let i = n; i < nVals; i++) {
          compileExpression(ctx, stmt.values[i]);
          emit(c, Op.POP, 1);
        }
      }
      break;
    }

    case "CompoundAssignmentStatement": {
      const opMap: Record<string, Op> = {
        "+": Op.ADD, "-": Op.SUB, "*": Op.MUL, "/": Op.DIV,
        "%": Op.MOD, "..": Op.CONCAT, "^": Op.POW,
        "//": Op.IDIV,
      };

      const baseOp = stmt.operator.replace("=", "");
      const binOp = opMap[baseOp];

      if (stmt.var.type === "Identifier") {

        compileExpression(ctx, stmt.var as unknown as Expression);
        compileExpression(ctx, stmt.value);
        if (binOp) emit(c, binOp);
        const slot = ctx.locals.get(stmt.var.name);
        if (slot !== undefined) {
          emit(c, Op.STORE_L, slot);
        } else {
          const upvalIdx = resolveUpvalue(ctx, stmt.var.name);
          if (upvalIdx !== null) {
            emit(c, Op.STORE_UPVAL, upvalIdx);
          } else {
            emit(c, Op.STORE_G, addConst(c, stmt.var.name));
          }
        }
      } else {

        const tempTable = allocFreshLocal(ctx, "cmpd_tbl");
        const tempKey = allocFreshLocal(ctx, "cmpd_key");
        if (stmt.var.type === "IndexExpression") {
          compileExpression(ctx, stmt.var.object);
          emit(c, Op.DUP);
          emit(c, Op.STORE_L, tempTable);
          compileExpression(ctx, stmt.var.index);
          emit(c, Op.DUP);
          emit(c, Op.STORE_L, tempKey);
        } else {
          compileExpression(ctx, (stmt.var as any).object);
          emit(c, Op.DUP);
          emit(c, Op.STORE_L, tempTable);
          emit(c, Op.PUSH_K, addConst(c, (stmt.var as any).property));
          emit(c, Op.DUP);
          emit(c, Op.STORE_L, tempKey);
        }

        emit(c, Op.GET_TABLE);

        compileExpression(ctx, stmt.value);
        if (binOp) emit(c, binOp);

        const tempVal = allocFreshLocal(ctx, "cmpd_val");
        emit(c, Op.STORE_L, tempVal);
        emit(c, Op.LOAD_L, tempTable);
        emit(c, Op.LOAD_L, tempKey);
        emit(c, Op.LOAD_L, tempVal);
        emit(c, Op.SET_TABLE);
      }
      break;
    }

    case "FunctionCallStatement": {
      const call = stmt.call as any;
      const callArgs: Expression[] = call.args || [];
      const isMethod = call.type === "MethodCallExpression" || (call.object && call.method);
      const spread = hasSpreadArg(callArgs);

      if (isMethod) {
        if (spread) {
          emit(c, Op.MARK);
          compileExpression(ctx, call.object);
          emit(c, Op.DUP);
          emit(c, Op.PUSH_K, addConst(c, call.method));
          emit(c, Op.GET_TABLE);
          emit(c, Op.SWAP);
          for (let i = 0; i < callArgs.length - 1; i++) compileExpression(ctx, callArgs[i]);
          compileSpreadLastArg(ctx, callArgs[callArgs.length - 1]);
          emit(c, Op.CALL_DYNAMIC, 1);
        } else {
          compileExpression(ctx, call.object);
          emit(c, Op.DUP);
          const idx = addConst(c, call.method);
          emit(c, Op.PUSH_K, idx);
          emit(c, Op.GET_TABLE);
          emit(c, Op.SWAP);
          for (const a of callArgs) compileExpression(ctx, a);
          emit(c, Op.CALL, callArgs.length + 1);
        }
      } else {
        if (spread) {
          emit(c, Op.MARK);
          compileExpression(ctx, call.callee || call);
          for (let i = 0; i < callArgs.length - 1; i++) compileExpression(ctx, callArgs[i]);
          compileSpreadLastArg(ctx, callArgs[callArgs.length - 1]);
          emit(c, Op.CALL_DYNAMIC, 1);
        } else {
          compileExpression(ctx, call.callee || call);
          for (const a of callArgs) compileExpression(ctx, a);
          emit(c, Op.CALL, callArgs.length);
        }
      }
      emit(c, Op.POP, 1);
      break;
    }

    case "DoStatement": {
      const prev = pushScope(ctx);
      for (const s of stmt.body) compileStatement(ctx, s);
      popScope(ctx, prev);
      break;
    }

    case "WhileStatement": {
      const condStart = c.code.length;
      pushLoop(ctx);
      compileExpression(ctx, stmt.condition);
      const jmpOut = c.code.length;
      emit(c, Op.JMP_F, 0);
      const prev = pushScope(ctx);
      const bodySlotStart = ctx.nextSlot;
      for (const s of stmt.body) compileStatement(ctx, s);
      const bodySlotEnd = ctx.nextSlot;
      popScope(ctx, prev);
      resolveContinues(ctx);

      for (let s = bodySlotStart; s < bodySlotEnd; s++) emit(c, Op.CLOSE_UPVAL, s);
      emit(c, Op.JMP, condStart);
      c.code[jmpOut + 1] = c.code.length;
      popLoop(ctx);
      break;
    }

    case "RepeatStatement": {
      const bodyStart = c.code.length;
      pushLoop(ctx);
      const prev = pushScope(ctx);
      const bodySlotStart = ctx.nextSlot;
      for (const s of stmt.body) compileStatement(ctx, s);
      const bodySlotEnd = ctx.nextSlot;
      resolveContinues(ctx);

      for (let s = bodySlotStart; s < bodySlotEnd; s++) emit(c, Op.CLOSE_UPVAL, s);
      compileExpression(ctx, stmt.condition);
      popScope(ctx, prev);

      const jmpBack = c.code.length;
      emit(c, Op.JMP_F, bodyStart);
      popLoop(ctx);
      break;
    }

    case "IfStatement": {
      const endJumps: number[] = [];

      compileExpression(ctx, stmt.condition);
      const jmpElse = c.code.length;
      emit(c, Op.JMP_F, 0);
      const prev = pushScope(ctx);
      for (const s of stmt.thenBody) compileStatement(ctx, s);
      popScope(ctx, prev);
      endJumps.push(c.code.length + 1);
      emit(c, Op.JMP, 0);
      c.code[jmpElse + 1] = c.code.length;

      for (const ec of stmt.elseifClauses) {
        compileExpression(ctx, ec.condition);
        const jmpNext = c.code.length;
        emit(c, Op.JMP_F, 0);
        const p2 = pushScope(ctx);
        for (const s of ec.body) compileStatement(ctx, s);
        popScope(ctx, p2);
        endJumps.push(c.code.length + 1);
        emit(c, Op.JMP, 0);
        c.code[jmpNext + 1] = c.code.length;
      }

      if (stmt.elseBody) {
        const p2 = pushScope(ctx);
        for (const s of stmt.elseBody) compileStatement(ctx, s);
        popScope(ctx, p2);
      }

      const end = c.code.length;
      for (const pos of endJumps) c.code[pos] = end;
      break;
    }

    case "ForNumericStatement": {
      const prev = pushScope(ctx);

      const hiddenCounter = allocFreshLocal(ctx, "forcount");
      const limitSlot = allocFreshLocal(ctx, "limit");
      const stepSlot = allocFreshLocal(ctx, "step");

      const counterSlot = allocLocal(ctx, stmt.var.name);

      compileExpression(ctx, stmt.start);
      emit(c, Op.STORE_L, hiddenCounter);
      compileExpression(ctx, stmt.end);
      emit(c, Op.STORE_L, limitSlot);
      compileExpression(ctx, stmt.step ?? { type: "NumberLiteral", value: "1", loc: stmt.loc });
      emit(c, Op.STORE_L, stepSlot);

      const condStart = c.code.length;

      emit(c, Op.LOAD_L, stepSlot);
      emit(c, Op.PUSH_K, addConst(c, 0));
      emit(c, Op.GT);
      const jmpNegCheck = c.code.length;
      emit(c, Op.JMP_F, 0);

      emit(c, Op.LOAD_L, hiddenCounter);
      emit(c, Op.LOAD_L, limitSlot);
      emit(c, Op.LE);
      const jmpEndPos = c.code.length;
      emit(c, Op.JMP_F, 0);
      const jmpToBody = c.code.length;
      emit(c, Op.JMP, 0);

      c.code[jmpNegCheck + 1] = c.code.length;
      emit(c, Op.LOAD_L, hiddenCounter);
      emit(c, Op.LOAD_L, limitSlot);
      emit(c, Op.GE);
      const jmpEndNeg = c.code.length;
      emit(c, Op.JMP_F, 0);

      c.code[jmpToBody + 1] = c.code.length;
      pushLoop(ctx);

      emit(c, Op.CLOSE_UPVAL, counterSlot);
      emit(c, Op.LOAD_L, hiddenCounter);
      emit(c, Op.STORE_L, counterSlot);

      const bodySlotStartNum = ctx.nextSlot;
      for (const s of stmt.body) compileStatement(ctx, s);
      const bodySlotEndNum = ctx.nextSlot;

      resolveContinues(ctx);

      for (let s = bodySlotStartNum; s < bodySlotEndNum; s++) emit(c, Op.CLOSE_UPVAL, s);

      emit(c, Op.LOAD_L, hiddenCounter);
      emit(c, Op.LOAD_L, stepSlot);
      emit(c, Op.ADD);
      emit(c, Op.STORE_L, hiddenCounter);

      emit(c, Op.JMP, condStart);

      const loopEnd = c.code.length;
      c.code[jmpEndPos + 1] = loopEnd;
      c.code[jmpEndNeg + 1] = loopEnd;

      popLoop(ctx);
      popScope(ctx, prev);
      break;
    }

    case "ForInStatement": {

      const iterCount = stmt.iter.length;
      const needed = 3;

      if (iterCount === 1 && isCallLike(stmt.iter[0])) {

        compileCallMulti(ctx, stmt.iter[0], needed);
      } else if (iterCount > 1 && isCallLike(stmt.iter[iterCount - 1])) {

        for (let i = 0; i < iterCount - 1; i++) compileExpression(ctx, stmt.iter[i]);
        const remaining = needed - (iterCount - 1);
        compileCallMulti(ctx, stmt.iter[iterCount - 1], remaining);
      } else {

        for (const e of stmt.iter) compileExpression(ctx, e);

        if (iterCount < needed) {
          for (let i = 0; i < needed - iterCount; i++) emit(c, Op.PUSH_NIL);
        }
      }

      const prev = pushScope(ctx);
      const __iter = allocFreshLocal(ctx, "iter");
      const __state = allocFreshLocal(ctx, "state");
      const __var = allocFreshLocal(ctx, "var");

      emit(c, Op.STORE_L, __var);
      emit(c, Op.STORE_L, __state);
      emit(c, Op.STORE_L, __iter);

      emit(c, Op.ITER_PREP, __iter, __state, __var);

      const varSlots = stmt.vars.map(v => allocLocal(ctx, v.name));
      const nVars = varSlots.length;

      const loopStart = c.code.length;
      pushLoop(ctx);

      for (const slot of varSlots) {
        emit(c, Op.CLOSE_UPVAL, slot);
      }

      emit(c, Op.LOAD_L, __iter);
      emit(c, Op.LOAD_L, __state);
      emit(c, Op.LOAD_L, __var);
      emit(c, Op.CALL_MULTI, 2, nVars);

      for (let i = nVars - 1; i >= 0; i--) {
        emit(c, Op.STORE_L, varSlots[i]);
      }

      emit(c, Op.LOAD_L, varSlots[0]);
      emit(c, Op.STORE_L, __var);

      emit(c, Op.LOAD_L, varSlots[0]);
      emit(c, Op.PUSH_NIL);
      emit(c, Op.NE);
      const jmpOut = c.code.length;
      emit(c, Op.JMP_F, 0);

      const bodySlotStartIn = ctx.nextSlot;
      for (const s of stmt.body) compileStatement(ctx, s);
      const bodySlotEndIn = ctx.nextSlot;

      resolveContinues(ctx);

      for (let s = bodySlotStartIn; s < bodySlotEndIn; s++) emit(c, Op.CLOSE_UPVAL, s);

      emit(c, Op.JMP, loopStart);

      c.code[jmpOut + 1] = c.code.length;

      popLoop(ctx);
      popScope(ctx, prev);
      break;
    }

    case "ReturnStatement": {
      if (stmt.values && stmt.values.length > 0) {
        const nVals = stmt.values.length;
        const lastVal = stmt.values[nVals - 1];

        if (nVals === 1 && isCallLike(lastVal) && !hasSpreadArg((lastVal as any).args) && ctx.parentCtx) {
          compileTailCall(ctx, lastVal);
        } else if (nVals === 1 && isCallLike(lastVal)) {

          compileCallMulti(ctx, lastVal, -1);
          emit(c, Op.RETURN, -1);
        } else if (nVals === 1 && lastVal.type === "VarargExpression") {

          emit(c, Op.LOAD_VARARG, -1);
          emit(c, Op.RETURN, -1);
        } else if (nVals > 1 && isCallLike(lastVal)) {

          for (let i = 0; i < nVals - 1; i++) compileExpression(ctx, stmt.values[i]);
          compileCallMulti(ctx, lastVal, -1);
          emit(c, Op.RETURN, -1);
        } else if (nVals > 1 && lastVal.type === "VarargExpression") {

          for (let i = 0; i < nVals - 1; i++) compileExpression(ctx, stmt.values[i]);
          emit(c, Op.LOAD_VARARG, -1);
          emit(c, Op.RETURN, -1);
        } else {

          for (const v of stmt.values) compileExpression(ctx, v);
          emit(c, Op.RETURN, nVals);
        }
      } else {
        emit(c, Op.RETURN, 0);
      }
      break;
    }

    case "BreakStatement": {
      const loop = currentLoop(ctx);
      if (loop) {
        loop.breakPatches.push(c.code.length + 1);
        emit(c, Op.JMP, 0);
      }
      break;
    }

    case "ContinueStatement": {
      const loop = currentLoop(ctx);
      if (loop) {
        loop.continuePatches.push(c.code.length + 1);
        emit(c, Op.JMP, 0);
      }
      break;
    }

    case "LocalFunctionStatement": {
      allocLocal(ctx, stmt.name);
      const proto = compileFunctionBody(ctx, stmt.params, stmt.body);
      emit(c, Op.CLOSURE, proto);
      emit(c, Op.STORE_L, ctx.locals.get(stmt.name)!);
      break;
    }

    case "FunctionStatement": {
      const fn = stmt.name;
      const params = fn.method
        ? [{ name: "self", variadic: false } as any, ...stmt.params]
        : stmt.params;
      const proto = compileFunctionBody(ctx, params, stmt.body);

      if (fn.method) {
        compileExpression(ctx, fn.base);
        emit(c, Op.PUSH_K, addConst(c, fn.method));
        emit(c, Op.CLOSURE, proto);
        emit(c, Op.SET_TABLE);
      } else if (fn.base.type === "Identifier") {
        const slot = ctx.locals.get(fn.base.name);
        emit(c, Op.CLOSURE, proto);
        if (slot !== undefined) {
          emit(c, Op.STORE_L, slot);
        } else {
          emit(c, Op.STORE_G, addConst(c, fn.base.name));
        }
      } else if (fn.base.type === "MemberExpression") {
        compileExpression(ctx, fn.base.object);
        emit(c, Op.PUSH_K, addConst(c, fn.base.property));
        emit(c, Op.CLOSURE, proto);
        emit(c, Op.SET_TABLE);
      }
      break;
    }

    case "TypeStatement":
    case "ExportTypeStatement":
    case "TypeFunctionStatement":
    case "ExportTypeFunctionStatement":
      break;

    default:
      break;
  }
}

export function compile(ast: Chunk): BytecodeChunk {
  const ctx = createContext();
  for (const stmt of ast.body) compileStatement(ctx, stmt);

  const lastStmt = ast.body.length > 0 ? ast.body[ast.body.length - 1] : null;
  if (!lastStmt || (lastStmt as any).type !== "ReturnStatement") {
    emit(ctx.chunk, Op.RETURN, 0);
  }
  return ctx.chunk;
}
