import type {
  Chunk,
  Statement,
  LastStatement,
  Expression,
  Var,
  Identifier,
  FuncName,
  Param,
} from "../ast/types.js";

const KEYWORDS = new Set([
  "and", "break", "continue", "do", "else", "elseif", "end", "export", "false",
  "for", "function", "if", "in", "local", "nil", "not", "or",
  "repeat", "return", "then", "true", "until", "while",
]);

const PRESERVED_GLOBALS = new Set([
  "_G", "game", "workspace", "script", "Players", "Instance", "Vector3", "Vector2",
  "CFrame", "Color3", "UDim2", "UDim", "Ray", "BrickColor", "Enum",
  "math", "string", "table", "typeof", "pairs", "ipairs", "next",
  "print", "warn", "error", "assert", "tick", "wait", "spawn",
  "getfenv", "setfenv", "newproxy", "rawequal", "rawget", "rawset",
  "select", "tonumber", "tostring", "type", "unpack", "xpcall",
  "loadstring", "load", "bit32",
]);

function isValidIdentifier(name: string): boolean {
  return /^[a-zA-Z_][a-zA-Z0-9_]*$/.test(name) && !KEYWORDS.has(name);
}

function generateName(index: number): string {
  if (index < 26) return String.fromCharCode(97 + index);
  let s = "";
  let n = index;
  while (n >= 0) {
    s = String.fromCharCode(97 + (n % 26)) + s;
    n = Math.floor(n / 26) - 1;
  }
  return s;
}

export interface ObfuscatorOptions {

  renameLocals?: boolean;

  preserveGlobals?: boolean;

  seed?: number;
}

const DEFAULT_OPTIONS: Required<ObfuscatorOptions> = {
  renameLocals: true,
  preserveGlobals: true,
  seed: 0,
};

export function obfuscate(ast: Chunk, options: ObfuscatorOptions = {}): Chunk {
  const opts = { ...DEFAULT_OPTIONS, ...options };
  if (!opts.renameLocals) return ast;

  const scope = new ScopeManager(opts);
  return transformChunk(ast, scope) as Chunk;
}

class ScopeManager {
  private flat: Map<string, string> = new Map();
  private undoStack: { name: string; prev: string | undefined }[][] = [[]];
  private nameCounter = 0;
  private opts: Required<ObfuscatorOptions>;

  constructor(opts: Required<ObfuscatorOptions>) {
    this.opts = opts;
  }

  pushScope(): void {
    this.undoStack.push([]);
  }

  popScope(): void {
    const undo = this.undoStack.pop()!;
    for (let i = undo.length - 1; i >= 0; i--) {
      const entry = undo[i]!;
      if (entry.prev === undefined) {
        this.flat.delete(entry.name);
      } else {
        this.flat.set(entry.name, entry.prev);
      }
    }
  }

  declare(name: string): string {
    if (!isValidIdentifier(name)) return name;
    if (this.opts.preserveGlobals && PRESERVED_GLOBALS.has(name)) return name;
    let newName: string;
    do {
      newName = generateName(this.nameCounter++);
    } while (KEYWORDS.has(newName));
    const prev = this.flat.get(name);
    this.undoStack[this.undoStack.length - 1]!.push({ name, prev });
    this.flat.set(name, newName);
    return newName;
  }

  resolve(name: string): string {
    if (!isValidIdentifier(name)) return name;
    if (this.opts.preserveGlobals && PRESERVED_GLOBALS.has(name)) return name;
    return this.flat.get(name) ?? name;
  }
}

function transformChunk(chunk: Chunk, scope: ScopeManager): Chunk {
  return {
    ...chunk,
    body: chunk.body.map((s) => transformStatement(s, scope)),
  };
}

function transformStatement(stmt: Statement | LastStatement, scope: ScopeManager): Statement | LastStatement {
  switch (stmt.type) {
    case "LocalStatement": {
      const values = stmt.values?.map((e) => transformExpression(e, scope));
      const vars = stmt.vars.map((v) => {
        const nv: any = {
          ...v,
          name: scope.declare(v.name),
        };
        if (v.type) nv.type = fixType(v.type, scope);
        return nv;
      });
      return { ...stmt, vars, values };
    }
    case "LocalFunctionStatement": {
      const name = scope.declare(stmt.name);
      scope.pushScope();
      const params = stmt.params.map((p) => {
        const np: any = {
          ...p,
          name: p.variadic ? "..." : scope.declare(p.name),
        };
        if (np.typeAnnotation) np.typeAnnotation = fixType(np.typeAnnotation, scope);
        return np;
      });
      const ret = stmt.returnType ? fixType(stmt.returnType, scope) : stmt.returnType;
      const body = stmt.body.map((s) => transformStatement(s, scope));
      scope.popScope();
      return { ...stmt, name, params, returnType: ret, body };
    }
    case "FunctionStatement": {
      const name = transformFuncName(stmt.name, scope);
      scope.pushScope();
      const params = stmt.params.map((p) => {
        const np: any = {
          ...p,
          name: p.variadic ? "..." : scope.declare(p.name),
        };
        if (np.typeAnnotation) np.typeAnnotation = fixType(np.typeAnnotation, scope);
        return np;
      });
      const ret = stmt.returnType ? fixType(stmt.returnType, scope) : stmt.returnType;
      const body = stmt.body.map((s) => transformStatement(s, scope));
      scope.popScope();
      return { ...stmt, name, params, returnType: ret, body };
    }
    case "ForNumericStatement": {
      scope.pushScope();
      const v = scope.declare(stmt.var.name);
      const varNode: Identifier = { type: "Identifier", name: v, loc: stmt.var.loc };
      const body = stmt.body.map((s) => transformStatement(s, scope));
      scope.popScope();
      return {
        ...stmt,
        var: varNode,
        start: transformExpression(stmt.start, scope),
        end: transformExpression(stmt.end, scope),
        step: stmt.step ? transformExpression(stmt.step, scope) : undefined,
        body,
      };
    }
    case "ForInStatement": {
      scope.pushScope();
      const vars = stmt.vars.map((v) => ({
        ...v,
        name: scope.declare(v.name),
      }));
      const body = stmt.body.map((s) => transformStatement(s, scope));
      scope.popScope();
      return {
        ...stmt,
        vars,
        iter: stmt.iter.map((e) => transformExpression(e, scope)),
        body,
      };
    }
    case "TypeStatement":
    case "ExportTypeStatement":
      return { ...stmt, value: fixType((stmt as any).value, scope) } as any;
    case "TypeFunctionStatement":
    case "ExportTypeFunctionStatement": {
      scope.pushScope();
      const params = stmt.params.map((p) => ({
        ...p,
        name: p.variadic ? "..." : scope.declare(p.name),
      }));
      const body = stmt.body.map((s) => transformStatement(s, scope));
      scope.popScope();
      return { ...stmt, params, body };
    }
    case "DoStatement":
      scope.pushScope();
      const doBody = stmt.body.map((s) => transformStatement(s, scope));
      scope.popScope();
      return { ...stmt, body: doBody };
    case "WhileStatement":
      scope.pushScope();
      const whileBody = stmt.body.map((s) => transformStatement(s, scope));
      scope.popScope();
      return {
        ...stmt,
        condition: transformExpression(stmt.condition, scope),
        body: whileBody,
      };
    case "RepeatStatement":
      scope.pushScope();
      const repeatBody = stmt.body.map((s) => transformStatement(s, scope));
      const repeatCond = transformExpression(stmt.condition, scope);
      scope.popScope();
      return {
        ...stmt,
        body: repeatBody,
        condition: repeatCond,
      };
    case "IfStatement":
      scope.pushScope();
      const thenBody = stmt.thenBody.map((s) => transformStatement(s, scope));
      const elseifClauses = stmt.elseifClauses.map((c) => ({
        condition: transformExpression(c.condition, scope),
        body: c.body.map((s) => transformStatement(s, scope)),
      }));
      const elseBody = stmt.elseBody?.map((s) => transformStatement(s, scope));
      scope.popScope();
      return {
        ...stmt,
        condition: transformExpression(stmt.condition, scope),
        thenBody,
        elseifClauses,
        elseBody,
      };
    case "AssignmentStatement":
      return {
        ...stmt,
        vars: stmt.vars.map((v) => transformVar(v, scope)),
        values: stmt.values.map((e) => transformExpression(e, scope)),
      };
    case "CompoundAssignmentStatement":
      return {
        ...stmt,
        var: transformVar(stmt.var, scope),
        value: transformExpression(stmt.value, scope),
      };
    case "FunctionCallStatement":
      return {
        ...stmt,
        call: transformExpression(stmt.call, scope) as any,
      };
    case "ReturnStatement":
      return {
        ...stmt,
        values: stmt.values?.map((e) => transformExpression(e, scope)),
      };
    default:
      return stmt;
  }
}

function transformFuncName(fn: FuncName, scope: ScopeManager): FuncName {
  const base = fn.base.type === "Identifier"
    ? { ...fn.base, name: scope.resolve(fn.base.name) }
    : transformExpression(fn.base, scope) as Identifier | import("../ast/types.js").MemberExpression;
  return { ...fn, base };
}

function transformVar(v: Var, scope: ScopeManager): Var {
  switch (v.type) {
    case "Identifier":
      return { ...v, name: scope.resolve(v.name) };
    case "IndexExpression":
      return {
        ...v,
        object: transformExpression(v.object, scope),
        index: transformExpression(v.index, scope),
      };
    case "MemberExpression":
      return {
        ...v,
        object: transformExpression(v.object, scope),
      };
    default:
      return v;
  }
}

function transformExpression(exp: Expression, scope: ScopeManager): Expression {
  switch (exp.type) {
    case "Identifier":
      return { ...exp, name: scope.resolve(exp.name) };
    case "BinaryExpression":
      return {
        ...exp,
        left: transformExpression(exp.left, scope),
        right: transformExpression(exp.right, scope),
      };
    case "UnaryExpression":
      return {
        ...exp,
        argument: transformExpression(exp.argument, scope),
      };
    case "CallExpression":
      return {
        ...exp,
        callee: transformExpression(exp.callee, scope),
        args: exp.args.map((a) => transformExpression(a, scope)),
      };
    case "MethodCallExpression":
      return {
        ...exp,
        object: transformExpression(exp.object, scope),
        args: exp.args.map((a) => transformExpression(a, scope)),
      };
    case "IndexExpression":
      return {
        ...exp,
        object: transformExpression(exp.object, scope),
        index: transformExpression(exp.index, scope),
      };
    case "MemberExpression":
      return {
        ...exp,
        object: transformExpression(exp.object, scope),
      };
    case "TableConstructor":
      return {
        ...exp,
        fields: exp.fields.map((f) => {
          if (f.kind === "index") return { ...f, index: transformExpression(f.index, scope), value: transformExpression(f.value, scope) };
          if (f.kind === "named") return { ...f, value: transformExpression(f.value, scope) };
          return { ...f, value: transformExpression(f.value, scope) };
        }),
      };
    case "FunctionExpression": {
      scope.pushScope();
      const params = exp.params.map((p) => ({
        ...p,
        name: p.variadic ? "..." : scope.declare(p.name),
      }));
      const body = exp.body.map((s) => transformStatement(s, scope));
      scope.popScope();
      return { ...exp, params, body };
    }
    case "ParenExpression":
      return { ...exp, expression: transformExpression(exp.expression, scope) };
    case "TypeAssertion":
      return {
        ...exp,
        expression: transformExpression(exp.expression, scope),
      };
    case "IfElseExpression":
      return {
        ...exp,
        condition: transformExpression(exp.condition, scope),
        thenExp: transformExpression(exp.thenExp, scope),
        elseifClauses: exp.elseifClauses.map((c) => ({
          condition: transformExpression(c.condition, scope),
          value: transformExpression(c.value, scope),
        })),
        elseExp: transformExpression(exp.elseExp, scope),
      };
    case "StringInterpolation":
      return {
        ...exp,
        parts: exp.parts.map((p) => (typeof p === "string" ? p : transformExpression(p, scope))),
      };
    default:
      return exp;
  }
}

function fixType(t: any, scope: ScopeManager): any {
  if (!t) return t;

  let out: any = t;

  if (t.type === "TypeofType") {
    out = { ...t, expression: transformExpression(t.expression, scope) };
  }
  else if (t.type === "TableType") {
    let props = t.props;
    if (props && props.length) {
      props = props.map((p: any) => {
        if (p.type === "TableIndexerType") {
          return { ...p, indexType: fixType(p.indexType, scope), valueType: fixType(p.valueType, scope) };
        }
        if (p.type === "TablePropType") {
          return { ...p, propType: fixType(p.propType, scope) };
        }
        return p;
      });
    }
    out = { ...t, props: props, arrayType: t.arrayType ? fixType(t.arrayType, scope) : t.arrayType };
  }
  else if (t.type === "FunctionType") {
    const params = t.params.map((p: any) => {
      if (p.type === "GenericTypePack") return p;
      if (p.type === "VariadicTypePack") return { ...p, inner: fixType(p.inner, scope) };
      return { ...p, type: fixType(p.type, scope) };
    });
    out = { ...t, params: params, returnType: fixType(t.returnType, scope) };
  }
  else if (t.type === "UnionType") {
    out = { ...t, types: t.types.map((x: any) => ({ ...x, type: fixType(x.type, scope) })) };
  }
  else if (t.type === "IntersectionType") {
    out = { ...t, types: t.types.map((x: any) => fixType(x, scope)) };
  }
  else if (t.type === "ParenType") {
    out = { ...t, inner: fixType(t.inner, scope) };
  }
  else if (t.type === "IdentifierType" && t.typeParams) {
    out = { ...t, typeParams: t.typeParams.map((x: any) => fixType(x, scope)) };
  }
  else if (t.type === "TypePack") {
    out = { ...t, types: t.types.map((x: any) => fixType(x, scope)) };
  }
  else if (t.type === "VariadicTypePack") {
    out = { ...t, inner: fixType(t.inner, scope) };
  }

  return out;
}
