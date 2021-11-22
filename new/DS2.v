Require Import List.
Require Import Strings.String.
Import StringSyntax.
Open Scope string.


  Inductive Ty :=
  | DP | S | ArrL : Ty -> Ty -> Ty
  | ArrR : Ty -> Ty -> Ty.

  Fixpoint ty_eq (t1 t2 : Ty) : {t1 = t2} + {t1 <> t2}.
    decide equality.
  Defined.

  Notation "x \ y" := (ArrL x y) (at level 40).
  Notation "x / y" := (ArrR x y).

  Definition VP := DP \ S.
  Definition TV := (DP \ S) / DP.

Module Ling.
  Parameter (E : Set).
  Parameter (mkE : string -> E).
  Parameter (eet : string -> E -> E -> Prop).
  Parameter (ett : string -> Prop -> E -> Prop).
  Parameter (et : string -> E -> Prop).
  Parameter (ERR : Prop).

  Definition addr := nat.

  Fixpoint val (t : Ty) : Type :=
    match t with
    | DP => E
    | S => Prop
    | ArrL t1 t2 => val t1 -> val t2
    | ArrR t1 t2 => val t2 -> val t1 end.

  Inductive exp : Ty -> Type :=
  | Val {t} : val t -> exp t
  | undefined {t} : exp t
  | everyone : exp DP
  | read (x : addr) (t : Ty) : exp t
  | store_cbv {t : Ty} : addr -> exp t -> exp t
  | store_cbn {t : Ty} : addr -> exp t -> exp t
  | compl {t1 t2 : Ty} : exp (t1) -> exp (t1 \ t2) -> exp (t2)
  | compr {t1 t2 : Ty} : exp (t1 / t2) -> exp (t2) -> exp (t1)
  .

  Coercion Val : val >-> exp.

  Notation "x <| y" := (compl x y) (at level 41).
  Notation "x |> y" := (compr x y) (at level 40).
                    
  Definition heap := forall (x : addr) (t : Ty), (exp t).

  Definition hset (x : addr) {t : Ty} (e : exp t) (h : heap) : heap.
   intros y t'.
   refine (if Nat.eqb x y then _ else h y t').
   destruct (ty_eq t t').
   rewrite <- e0; apply e.
   apply (h y t').
  Defined.

  Definition heap0 : heap := fun _ _ => undefined.

  Inductive Div A := | OK : A -> Div A | OutOfFuel : Div A.
  Arguments OK [A].
  Arguments OutOfFuel {A}.

  Inductive Comp : Type -> Type :=
  | Ret {A} : A -> Comp A
  | Err {A} {t} : string -> exp t -> Comp A
  | Forall {A} : (A -> Comp Prop) -> Comp Prop.            

  Fixpoint interp (fuel : nat) {t} (e : exp t) (hp : heap) {struct fuel} :
    ((val t -> heap -> Comp Prop) -> Comp Prop) :=
    match fuel with
      | 0 => fun _ => Err "out of fuel" e
      | Datatypes.S fuel =>
        match e in exp t1 return (((val t1) -> heap -> Comp Prop) -> Comp Prop) with
        | Val v => (fun k => (k v hp))
        | undefined => (fun _ => @Err _ t "undefined" undefined)
        | everyone => (fun (k : E -> heap -> Comp Prop) =>
                            Forall (fun x => k x hp))
        | read x t =>
           interp fuel (hp x t) hp
        | store_cbv x e => fun k =>
                (interp fuel e hp) (fun v hp' =>
                           k v (hset x (Val v) hp'))
        | store_cbn x e => fun k =>
          (interp fuel e hp) (fun v hp' =>
                           k v (hset x e hp'))     
        | compl e1 e2 => fun k =>
                (interp fuel e1 hp) (fun x hp' =>
                        (interp fuel e2 hp') (fun f hp'' =>
                                k (f x) hp''))      
        | compr e2 e1 => fun k =>
                (interp fuel e1 hp) (fun x hp' =>
                        (interp fuel e2 hp') (fun f hp'' =>
                                k (f x) hp''))      
            end end.


  Definition vp (s : string) : exp VP := @Val VP (et s).
  Definition dp (s : string) : exp DP := @Val DP (mkE s).

  Definition Interp {t} (e : exp t) (hp : heap) := interp 8 e hp.


  Definition eval (e : exp S) : (Comp Prop) :=
    Interp e (fun _ _ => undefined) (fun s _ => Ret s).

  Definition he (x : addr) := read x DP.

  Definition knows : exp TV :=
    @Val TV (eet "knows").
  Definition thinks : exp ((DP \ S) / S) :=
    @Val ((DP \ S) / S) (ett "thinks").

  Parameter (Of : E -> E -> E).
  Definition s : exp ((DP \ DP) / DP) :=
    @Val ((DP \ DP) / DP) Of.

  Compute (eval (everyone <| (vp "sleeps"))).

  Compute (eval (store_cbv 0 everyone <| (knows |> he 0))).
                              
  Definition thinks_he_will_win : exp VP :=
    store_cbn 1 (thinks |> (he 0 <| vp "will_win")).

  Definition johns_coach :=
    store_cbv 0 (dp "john") <| (s |> dp "coach").

  Compute (eval (johns_coach <| thinks_he_will_win)).

  Definition bills_coach_too :=
    (dp "bill" <| (s |> dp "coach")) <| (read 1 VP).

  Definition and : exp ((S \ S) / S) :=
    @Val ((S \ S) / S) (fun x y => x /\ y).

  Compute (eval ((johns_coach <| thinks_he_will_win) <| (and |> bills_coach_too))).



    

  
