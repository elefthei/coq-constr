Require Import
        String
        Nat
        Coq.Init.Datatypes
        Coq.FSets.FMapList
        Coq.Structures.OrderedTypeEx.

Module Import M := FMapList.Make(String_as_OT).
Open Scope string_scope.

Definition Env := M.t nat.
Definition Clean := empty nat.

Section R1C.
  (** Finite field modulo prime P *)
  Parameter P: nat.
  Parameter (H: forall n: nat, Nat.modulo P n = 0).

  (** ADT for R1Constraint *)
  Inductive R1C :=
  | Const (n: nat)
  | Mult (n: nat) (v: string)
  | Neg (inner: R1C)
  | Plus (left: R1C) (right: R1C).

  Definition R1CS := list R1C.

  (** Syntax *)  
  Declare Scope r1c_scope.
  Bind Scope r1c_scope with R1C.
  Open Scope r1c_scope.
  Coercion Const : nat >-> R1C.      
  Definition string_to_r1c(s: string) := Mult 1 s.
  Coercion string_to_r1c: string >-> R1C.

  Notation "a * e" := (Mult a e) (at level 40, left associativity): r1c_scope.
  Notation "e1 + e2" := (Plus e1 e2) (at level 50, left associativity): r1c_scope.
  Notation "- e" := (Neg e) (at level 35, right associativity): r1c_scope.
  Notation "e1 == e2" := (Plus e1 (Neg e2)) (at level 55, left associativity): r1c_scope.

  (** Let's try it out *)
  Compute "r0"  == 0 + 1.

  (** Check a valuation satisfies an R1CS *)
  Definition check(env: Env)(C: R1CS): Prop.
    Admitted.
End R1C.

Section Expr.
  Declare Scope asm_scope.
  Open Scope asm_scope.
  
  (** AST of small assembly language *)
  Inductive AsmExpr :=
  | AAdd (dst: string) (src: string)
  | ASub (dst: string) (src: string)
  | AMult (dst: string) (src: string)
  | AMov (dst: string) (const: nat)
  | ASeq (head: AsmExpr) (tail: AsmExpr).

  Infix "|" := ASeq (at level 55): asm_scope.
  Bind Scope asm_scope with AsmExpr.
  
  (** Program: r0 <- 0 + 1 *)
  Compute AMov "%r0" 0
          | AMov "%r1" 1
          | AAdd "%r0" "%r1".
    
  Definition eval(env: Env)(p: AsmExpr): Env :=
    match p with
    | AAdd l r => match (find l env, find r env) with
                 | (Some lv, Some rv) => add l (lv + rv) env
                 | (None, Some rv) => add l rv env
                 | _ => None
                 end
    | ASub l r => match (find l env, find r env) with
                 | (Some lv, Some rv) => add l (lv - rv) env
                 | _ => None
                 end
    | AMult r v => match (find l env, find r env) with
                 | (Some lv, Some rv) => add l (lv * rv) env
                 | _ => None
                  end
    | AMov reg v => add reg v env
    | ASeq a b => eval (eval env a) b
    end.
  
End Expr.

Set Implicit Arguments.

Section AbstrInterp.

  Definition simulation(P: AsmExpr)(C: R1CS) := forall (env: map string nat),
      env = nil -> let endState := eval env P in check endState C.
           
  
