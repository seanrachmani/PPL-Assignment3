import { isNumExp, isBoolExp, isVarRef, isPrimOp, isProgram, isDefineExp, isVarDecl,
    isAppExp, isStrExp, isIfExp, isProcExp, isLetExp, isLitExp, isLetrecExp, isSetExp,
    parseL5Exp, unparse, Exp, parseL5 } from "../../src/L5/L5-ast";
import { Result, bind, isFailure, isOk, isOkT, makeFailure, makeOk, mapv } from "../../src/shared/result";
import { applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "../../src/L5/TEnv";
import { parse as parseSexp } from "../../src/shared/parser";
import { typeofPrim, typeofExp, typeofProgram } from "../../src/L5/L5-typecheck";
import { isBoolTExp, isListTExp, isNumTExp, isProcTExp, isStrTExp, isTVar, makeListTExp, makeNumTExp, makeTVar, parseTE, parseTExp, TExp, unparseTExp } from "../../src/L5/TExp";
import { checkNoOccurrence } from "../../src/L5/L5-substitution-adt";
import * as S from "../../src/L5/L5-substitution-adt";
import { inferType } from "../../src/L5/L5-type-equations";
import { isNone, isSome, Optional } from "../../src/shared/optional";
import { sub } from "./test-helpers";

const p = (x: string): Result<Exp> => bind(parseSexp(x), parseL5Exp);

export const L5typeofProgram = (concreteExp: string): Result<string> =>
    bind(parseL5(concreteExp), (e: Program) =>
        bind(typeofProgram(e, makeEmptyTEnv()), unparseTExp));

export const L5typeof = (concreteExp: string): Result<string> =>
    bind(p(concreteExp), (e: Exp) => 
            bind(typeofExp(e, makeEmptyTEnv()), unparseTExp));

describe('L5-typecheck', () => {

    it('typeofPrim - cons', () => {
        const tcons = bind(p("cons"), (e: Exp) => isPrimOp(e) ? typeofPrim(e) : makeFailure(`Expected PrimOp: cons`));
        expect(tcons).toSatisfy(isOkT(isProcTExp));
        expect(bind(tcons, (x) =>
            isProcTExp(x) ? makeOk(x.paramTEs.length) : makeFailure("not ProcTExp")
            )).toEqual(makeOk(2));
    });

    it('typeofPrim - car', () => {
        const tcar = bind(p("car"), (e: Exp) => isPrimOp(e) ? typeofPrim(e) : makeFailure(`Expected PrimOp : car`));
        expect(tcar).toSatisfy(isOkT(isProcTExp));
        expect(bind(tcar, (x) =>
            isProcTExp(x) ? makeOk(x.paramTEs.length) : makeFailure("not ProcTExp")
            )).toEqual(makeOk(1));
    });

    it('typeofPrim - cdr', () => {
        const tcdr = bind(p("cdr"), (e: Exp) => isPrimOp(e) ? typeofPrim(e) : makeFailure(`Expected PrimOp: cdr`));
        expect(tcdr).toSatisfy(isOkT(isProcTExp));
        expect(bind(tcdr, (x) =>
            isProcTExp(x) ? makeOk(x.paramTEs.length) : makeFailure("not ProcTExp")
            )).toEqual(makeOk(1));
    });
});

describe('L5-substitution-adt', () => {
    it('checkNoOccurrence', () => {
        expect(checkNoOccurrence(makeTVar("x"), makeListTExp(makeTVar("x")))).toSatisfy(isFailure);
        expect(checkNoOccurrence(makeTVar("x"), makeListTExp(makeTVar("y")))).toEqual(makeOk(true));
    });

    it('applySub - single subtitution', () => {
        const sub1 = sub(["X"], ["boolean"]);
        const texp = "(list X)";
        const te1 = parseTE(texp);
        const unparsed = bind(sub1, (sub: S.Sub) =>
                                bind(te1, (te: TExp) =>
                                    unparseTExp(S.applySub(sub, te))));
        expect(unparsed).toEqual(makeOk("(list boolean)"));
    });
});

describe('L5-typecheck - define', () => {
    it('should correctly type a boolean definition', () => {
        expect(L5typeof("(define (x : boolean) (if (> 1 2) #t #f))")).toEqual(makeOk("void"));
    });

    it('should correctly type a number definition', () => {
        expect(L5typeof("(define (x : number) 5)")).toEqual(makeOk("void"));
    });

    it('should fail on type mismatch in define (Negative Test)', () => {
        expect(L5typeof("(define (x : boolean) 5)")).toSatisfy(isFailure);
    });
});

describe('L5-typecheck - program type', () => {
    it('should correctly type a simple program with number', () => {
        expect(L5typeofProgram("(L5 (define (x : number) 5) (+ x 1))")).toEqual(makeOk("number"));
    });

    it('should correctly type a simple program with boolean', () => {
        expect(L5typeofProgram("(L5 (define (x : boolean) #t) x)")).toEqual(makeOk("boolean"));
    });

    it('should fail if program last expression has a type error (Negative Test)', () => {
        expect(L5typeofProgram("(L5 (define (x : number) 5) (+ x #t))")).toSatisfy(isFailure);
    });
});

describe('L5-type-equations - list inference', () => {
    const infer = (src: string): Optional<TExp> => {
        const parsed = p(src);
        if (parsed.tag !== "Ok") throw new Error(`parse failed: ${src}`);
        return inferType(parsed.value);
    };

    it('infers (list number) for cons of number into list literal via lambda app', () => {
        const t = infer("((lambda ((xs : (list number))) (cons 0 xs)) '(1 2 3))");
        expect(isSome(t) && isListTExp(t.value) && isNumTExp(t.value.itemTE)).toBe(true);
    });

    it('infers number for car of list number', () => {
        const t = infer("((lambda ((xs : (list number))) (car xs)) '(1 2 3))");
        expect(isSome(t) && isNumTExp(t.value)).toBe(true);
    });

    it('infers (list boolean) for empty list when unified with a boolean list', () => {
        const t = infer("((lambda ((xs : (list boolean))) xs) '())");
        expect(isSome(t) && isListTExp(t.value) && isBoolTExp(t.value.itemTE)).toBe(true);
    });
});

describe('L5-typecheck - DefineExp final type', () => {
    it('(define (x : number) 5) is void', () => {
        expect(L5typeof("(define (x : number) 5)")).toEqual(makeOk("void"));
    });

    it('(define (b : boolean) #t) is void', () => {
        expect(L5typeof("(define (b : boolean) #t)")).toEqual(makeOk("void"));
    });
});

describe('L5-typecheck - Program final return type', () => {
    it('(L5 5) returns number', () => {
        expect(L5typeofProgram("(L5 5)")).toEqual(makeOk("number"));
    });

    it('(L5 (define (x : number) 5) (+ x 1)) returns number', () => {
        expect(L5typeofProgram("(L5 (define (x : number) 5) (+ x 1))"))
            .toEqual(makeOk("number"));
    });
});

describe('L5-Integration - Comprehensive Program Typecheck', () => {
    it('should correctly type-check the comprehensive PPL program as number', () => {
const bigProgram = `
        (L5
            (define (a : number) 1)

            (define (square : (number -> number))
                (lambda ((x : number)) : number (* x x)))

            (define (let-result : number)
                (let (((p : boolean) #t) ((q : number) 7))
                    (if p q (+ q q))))

            (define (fact : (number -> number))
                (letrec (((f : (number -> number))
                        (lambda ((n : number)) : number
                            (if (= n 0)
                                1
                                (* n (f (- n 1)))))))
                f))

            (define (make-adder : (number -> (number -> number)))
                (lambda ((n : number)) : (number -> number)
                    (lambda ((x : number)) : number (+ n x))))

            (define (add10 : (number -> number)) (make-adder 10))

            (+ (square 4) (+ (fact 5) (+ let-result (add10 3))))
        )`;
        expect(L5typeofProgram(bigProgram)).toEqual(makeOk("number"));
    });
});