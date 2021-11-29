Require Import List.
Require Import Strings.String.
Import StringSyntax.
Open Scope string.



(* Comp is like Prop, but it allows for runtime errors in the interpreter and quantification. *)
  Inductive Comp : Type :=
  | Ret : Prop -> Comp 
  | Err : string -> Comp 
  | Forall {A} : (A -> Comp ) -> Comp.            

(* Used for sequencing two Comp's. *)
  Fixpoint bind_comp (c : Comp) (f : Prop -> Comp) : Comp :=
    match c with
    | Ret x => f x
    | Err s => Err s
    | Forall f' => Forall (fun x => bind_comp (f' x) f) end.

(* Conjunct two Comp's. *)
  Definition and_comp (c1 c2 : Comp) : Comp :=
    bind_comp c1 (fun p => bind_comp c2 (fun q => Ret (p /\ q))).


  Inductive Ty :=
  | DP | S | ArrL : Ty -> Ty -> Ty
  | ArrR : Ty -> Ty -> Ty
  .

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

  Definition alt (p0 : Comp) (f : E -> Comp) (x : E) : Comp :=
    Ret (exists y, p0 = f y /\ x <> y).

  Definition addr := nat.

  Fixpoint val (t : Ty) : Type :=
    match t with
    | DP => E
    | S => Comp
    | ArrL t1 t2 => val t1 -> val t2
    | ArrR t1 t2 => val t2 -> val t1
                                  end.

  
(* Expressions of the language. *) 
  Inductive exp : Ty -> Type :=
  | Val {t} : val t -> exp t (* inject pure values *)
  | undefined {t} : exp t (* undefined *)
  | everyone : exp DP 
  | read (x : addr) (t : Ty) : exp t
  | store_cbv {t : Ty} : addr -> exp t -> exp t  (* explained below *)
  | store_cbn {t : Ty} : addr -> exp t -> exp t
  | compl {t1 t2 : Ty} : exp (t1) -> exp (t1 \ t2) -> exp (t2) (* compose left *)
  | compr {t1 t2 : Ty} : exp (t1 / t2) -> exp (t2) -> exp (t1) (* compose right *)
  | foc (s : addr) : exp DP -> exp DP
  | force : exp S -> exp S
  .


  Coercion Val : val >-> exp.

  Notation "x <| y" := (compl x y) (at level 41).
  Notation "x |> y" := (compr x y) (at level 40).


(*
  The heap is interacted with through the read, store_cbv, and store_cbn expressions. 

Read takes in a heap index and a type, and returns an expression of that type (possibly undefined).

store_cbv and store_cbn are similar, but differ on what they actually store in the heap. Consider the following:

store_X (read 1 DP) 0 DP

if X is cbv, then the heap at index 0 will be exactly what's at index 1 at this point in time. Thus if 1 is changed later, 0 will stay the sae.

If X is cbn, then the heap at index 0 will  simply be the expression "read 1 DP". Thus if 1 is changed later, reading from index 0 will read the updated value. 
*)

  Definition heap := forall (x : addr) (t : Ty), (exp t).

  Definition hset (x : addr) {t : Ty} (e : exp t) (h : heap) : heap.
   intros y t'.
   refine (if Nat.eqb x y then _ else h y t').
   destruct (ty_eq t t').
   rewrite <- e0; apply e.
   apply (h y t').
  Defined.

  Definition heap0 : heap := fun _ _ => undefined.


  (* We give expression semantics through an interpretation function.
  You can ignore the fuel component, it's only there to make Coq accept
the function as terminating. 

   The semantics of expressions is mostly standard. The semantics is
continuation-passing, but it also keeps track of the heap. The heap is like the Ctx from before, but less information is tracked statically about what's in the heap. *)


  Fixpoint interp (fuel : nat) {t} (e : exp t) (hp : heap) {struct fuel} :
    ((val t -> heap -> Comp ) -> Comp ) :=
    match fuel with
      | 0 => fun _ => Err "out of fuel" 
      | Datatypes.S fuel =>
        match e in exp t1 return (((val t1) -> heap -> Comp ) -> Comp) with
        | Val v => (fun k => (k v hp))
        | undefined => (fun _ => Err "undefined" )
        | everyone => (fun (k : E -> heap -> Comp) =>
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
        (* 
  The semantics of foc takes in a propositional antecedent, given by heap index s,
  and does the following: 
  it behaves as the underlying expression, but also uses its continuation k to
  compute the focus alternatives. Thus we say that s is in the focus set of k,
  but differs by the value of x. *) 
        | foc s e => fun k =>
          (interp fuel (hp s S) hp) (fun s0 _ => 
            (interp fuel e hp) (fun x hp' =>
                                  and_comp (k x hp')
                                           (alt s0 (fun x => k x hp') x)))
    (* Force is like LIFT + LOWER. It delineates a continuation so it cannot scope over the entire matrix clause, but only the subclause we care about. *)                                    
        | force e => fun k =>
           k ((interp fuel e hp) (fun s hp' => s)) hp
            end end.


  Definition vp (s : string) : exp VP := @Val VP (fun x => Ret (et s x)).
  Definition dp (s : string) : exp DP := @Val DP (mkE s).

  Definition Interp {t} (e : exp t) (hp : heap) := interp 15 e hp.


  Definition eval (e : exp S) : (Comp ) :=
    Interp e (fun _ _ => undefined) (fun s hp => s ).

  Definition he (x : addr) := read x DP.

  Definition knows : exp TV :=
    @Val TV (fun x y => Ret (eet "knows" x y)).
  Definition thinks : exp ((DP \ S) / S) :=
    @Val ((DP \ S) / S) (fun x y =>
                           bind_comp x (fun x =>
                              Ret (ett "thinks" x y))).

  Parameter (Of : E -> E -> E).

  (* 's  *)
  Definition s : exp ((DP \ DP) / DP) :=
    @Val ((DP \ DP) / DP) Of.

  Compute (eval (everyone <| (vp "sleeps"))).

  Compute (eval (store_cbv 0 everyone <| (knows |> he 0))).

  Definition johns_coach :=
    store_cbv 0 (dp "john") <| (s |> dp "coach").
                              
  Definition thinks_he_will_win : exp VP :=
    store_cbn 0 (thinks |> (he 0 <| vp "will_win")).

  Compute (eval (johns_coach <| thinks_he_will_win)).

  Definition bills_coach_too :=
    (store_cbv 0 (foc 1 (dp "bill")) <| (s |> dp "coach")) <| (read 0 VP).

  Definition and : exp ((S \ S) / S) :=
    @Val ((S \ S) / S) (fun x y => and_comp x y).

  Compute (eval (store_cbv 1 (johns_coach <| thinks_he_will_win) <| (and |> (force (bills_coach_too))))).

  (*
    simplified, we get: 

    thinks (will_win bill) (bill's coach) /\
    thinks (will_win john) (john's coach) /\
    (exists x,
       (thinks (will_win john) (john's coach) =
        thinks (will_win x) (x's coach) /\
        x != bill)) *)
    



  
