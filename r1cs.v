Require Import
        String
        Coq.ZArith.ZArith
        Coq.ZArith.BinIntDef
        Coq.Init.Datatypes
        Coq.FSets.FMapList
        Coq.Structures.OrderedTypeEx.

Print Z.
Locate of_nat.
Open Scope Z_scope.

Module L := Coq.Lists.List.
Module M := FMapList.Make(String_as_OT).

Open Scope string_scope.
Set Implicit Arguments.

Definition Env := M.t Z.
Definition Clean := M.empty Z.

Section R1C.
  (** Finite field modulo prime P *)
  Parameter P: Z.
  Parameter (H: forall n: Z, Z.modulo P n = 0).

  (** ADT for R1Constraint *)
  Inductive R1C :=
  | Const (n: Z)
  | Mult (n: Z) (v: string)
  | Neg (inner: R1C)
  | Plus (left: R1C) (right: R1C).

  Definition R1CS := list R1C.

  (** Syntax *)  
  Declare Scope r1c_scope.
  Bind Scope r1c_scope with R1C.
  Open Scope r1c_scope.
  Coercion Const : Z >-> R1C.      
  Definition string_to_r1c(s: string) := Mult 1 s.
  Coercion string_to_r1c: string >-> R1C.

  Notation "a * e" := (Mult a e) (at level 40, left associativity): r1c_scope.
  Notation "e1 + e2" := (Plus e1 e2) (at level 50, left associativity): r1c_scope.
  Notation "- e" := (Neg e) (at level 35, right associativity): r1c_scope.
  Notation "e1 == e2" := (Plus e1 (Neg e2)) (at level 55, left associativity): r1c_scope.

  (** Let's try it out *)
  Definition ex1_equation := "r0"  == 0 + 1.

  Fixpoint substitute(env: Env)(constr: R1C) : option Z :=
    match constr with
    | Mult n v => match M.find v env with
                 | None => None
                 | Some v' => Some (Z.mul n v')
                 end
    | Plus l r => match substitute env l, substitute env r with
                 | Some a, Some b => Some (Z.add a b)
                 | _, _ => None
                 end
    | Neg i => option_map Z.opp (substitute env i)
    | Const n => Some n
    end.

  (** Check a valuation satisfies an R1CS *)
  Definition check(env: Env)(C: R1CS): Prop := L.Forall (fun r1c => substitute env r1c = Some 0) C.
  
End R1C.

Section Expr.
  Declare Scope asm_scope.
  Open Scope asm_scope.
  
  (** AST of small assembly language *)
  Inductive AsmExpr :=
  | AAdd (dst: string) (src: string)
  | ASub (dst: string) (src: string)
  | AMult (dst: string) (src: string)
  | AMov (dst: string) (const: Z)
  | ASeq (head: AsmExpr) (tail: AsmExpr).

  Infix ";;" := ASeq (at level 55): asm_scope.
  Bind Scope asm_scope with AsmExpr.
  
  (** Program: r0 <- 0 + 1 *)
  Definition ex1_prog :=
    AMov "%r0" 0 ;;
    AMov "%r1" 1 ;;
    AAdd "%r0" "%r1".

  Fixpoint eval(env: Env)(p: AsmExpr): Env :=
    match p with
    | AAdd l r => match M.find l env, M.find r env with
                 | Some lv, Some rv => M.add l (lv + rv) env
                 | None, Some rv => M.add l rv env
                 | _, _ => env
                 end
    | ASub l r => match M.find l env, M.find r env with
                 | Some lv, Some rv => M.add l (lv - rv) env
                 | _, _ => env
                 end
    | AMult l r => match M.find l env, M.find r env with
                  | Some lv, Some rv => M.add l (lv * rv) env
                  | _, _ => env
                  end
    | AMov reg v => M.add reg v env
    | ASeq a b => eval (eval env a) b
    end.
  
End Expr.

Require Import Coq.FSets.FMapFacts.

Module P := WProperties_fun String_as_OT M.
Module F := P.F.

Section AbstrInterp.

  Definition simulation_correct(P: AsmExpr)(C: R1CS) := forall (env: Env),
    let endState := eval env P in check endState C.

  Theorem some_example_correct:
    simulation_correct ex1_prog (L.cons ex1_equation L.nil).
  Proof.
    unfold simulation_correct.
    intros.
    simpl.
    replace (
    rewrite F.add_eq_o.
  Admitted.
  
    
    rewrite F.add_eq_o.
    F.map_iff
End AbstrInterp.
