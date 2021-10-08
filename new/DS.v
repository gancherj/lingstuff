Require Import List.
Require Import Strings.String.
Import StringSyntax.
Open Scope string.

  Inductive Ty :=
  | dp | s | ArrL : Ty -> Ty -> Ty
  | ArrR : Ty -> Ty -> Ty
  | Comp : Ctx -> Ty -> Ctx -> Ty
  with
    Ctx := | Empty | Cons : Ctx -> Ty -> Ctx.

Module Ling.
  Parameter (E : Type).
  Parameter (e : string -> E).
  Parameter (eet : string -> E -> E -> Prop).
  Parameter (et : string -> E -> Prop).
  Parameter (baseAdj : string -> E -> Prop).
  Parameter (Wants : Prop -> E -> Prop).
  Parameter (Knows : Prop -> E -> Prop).
  Parameter (know : E -> Prop -> Prop).
  Parameter (Mother : E -> E).      

  Fixpoint interpTy (t : Ty) :=
    match t with
    | dp => E
    | s => Prop
    | ArrL x y => interpTy x -> interpTy y
    | ArrR x y => interpTy y -> interpTy x
    | Comp G t D =>
      (interpCtx D -> interpTy t -> Prop) -> interpCtx G -> Prop
                                                                            end
    with
    interpCtx (g : Ctx) := 
      match g with
      | Empty => unit
      | Cons g' t => interpCtx g' * interpTy t end.
      
  Coercion interpTy : Ty >-> Sortclass.
  Coercion interpCtx : Ctx >-> Sortclass.

  Notation "x \ y" := (ArrL x y) (at level 40).
  Notation "x / y" := (ArrR x y).

  Notation "G |- t -| D" := (Comp G t D) (at level 30).
  Notation "<>" := (Empty).
  Notation "G ;; t" := (Cons G t) (at level 29, left associativity, format "G  ';;'  t").

  Parameter (alt : Prop -> ((interpTy dp) -> Prop) -> (interpTy dp) -> Prop).


  (* Some helper typeclasses.
     This first one, Proj, turns one larger discourse into another smaller discourse.
     If the mapping is ambiguous, it prefers the mapping using the most recent variables. *)
  
  (* This order of writing Proj down gets the most recent discourse referent that fits. This should be more programmable *)
  Class Proj (G1 G2 : Ctx) := proj : G1 -> G2.
  Instance proj_refl g : Proj g g := fun x => x.
  Instance proj_cons_different g1 g2 t `{Proj g1 g2} : Proj (g1 ;; t) g2 := 
    fun g1t =>
      proj (fst g1t).
  Instance proj_cons_same g1 g2 t `{Proj g1 g2} : Proj (g1 ;; t) (g2 ;;t) := 
    fun g1t =>
      (proj (fst g1t), snd g1t).

  Fixpoint getCtx (G: Ctx) (i : nat) : option Ty :=
    match G with
    | Empty => None
    | Cons g' t =>
      match i with
      | 0 => Some t
      | S i' => getCtx g' i' end end.

  Class GetCtx G i t := getCtx_witness : getCtx G i = Some t.
  Instance GetCtx_last G t : GetCtx (G ;; t) 0 t := eq_refl.
  Instance GetCtx_next G t t2 i `{GetCtx G i t} : GetCtx (G ;; t2) (S i) t := @getCtx_witness G i t _.

  Definition typeAt (G: Ctx) (i : nat) : Type :=
    match getCtx G i with
    | None => unit
    | Some  t => t end.

  Fixpoint recall' (G : Ctx) (i : nat) : interpCtx G -> typeAt G i.
    destruct G.
    apply (fun x => x).
    destruct i.
    apply (fun g => snd g).
    apply (fun g => recall' G i (fst g)).
  Defined.

  Definition recall (G : Ctx) (i : nat) (t : Ty) `{GetCtx G i t} : interpCtx G -> t.
    remember (recall' G i) as p.
    clear Heqp.
    unfold typeAt in p.
    rewrite H in p.
    apply p.
  Defined.

  Definition lift {t : Ty} {G : Ctx} (x : t) : G |- t -| G := 
    fun k g => k g x.

  (* You can lower and evaluate any sentence that doesn't have any free variables in it. *)
  Definition lower {D} (c : <> |- s -| D): s :=
    (c (fun _ p => p) tt).

  (* Lifting the arrow combinators to computations, just like 'cleft' and 'cright' as before. *)

  Definition compL {G D E : Ctx} {t1 t2 : Ty}
             (X : G |- t1 -| D)
             (Y : D |- t1 \ t2 -| E) : G |- t2 -| E :=
    (fun k g => X (fun d x => Y (fun e f => k e (f x)) d) g).

  Definition compR {G D E : Ctx} {t1 t2 : Ty} (X : G |- t1 / t2 -| D) (Y : D |- t2 -| E) : G |- t1 -| E :=
    (fun k g => X (fun d f => Y (fun e x => k e (f x)) d) g).

  Notation "x <| y" := (compL x y) (at level 41).
  Notation "x |> y" := (compR x y) (at level 40).




  Definition tv st : (dp \ s) / dp := eet st.
  Definition iv st : dp \ s := et st.

  Definition everyone {G : Ctx} : G |- dp -| G :=
    fun k g => forall x, k g x. 

  Definition someone {G : Ctx} : G |- dp -| G;;dp :=
    fun k g => exists x, k (g, x) x. 

  Definition everyone_sleeps : <> |- s -| <> :=
    everyone <| lift (iv "sleeps").

  Eval compute in (lower everyone_sleeps).
  (* forall x, et "sleeps" x *)


  (** Evaluation order stuff **)

  (* Force runs the first argument, and returns a dummy version to be used later. *)
  Definition force {G D} {t t'}
             (c : G |- t -| D)
             (f : G |- t -| D -> G |- t' -| D) : G |- t' -| D :=
  (fun k g => c (fun d x => f (fun f0 _ => f0 d x) k g) g).

  (* everyone loves someone *)
  Eval compute in (lower (everyone <| lift (tv "loves") |> someone)).

  (* The inverse reading is done using this 'force' combinator. There are likely more 
     natural encodings of reverse evaluation order as well. Maybe the verb induces inverse evaluation? *)
  Eval compute in (lower
                     (force someone
                    (fun s => everyone <| lift (tv "loves") |> s))).

  Definition mk_dp s : dp := e s.
  Definition john := mk_dp "john".
  Definition alice := mk_dp "alice".


  (* The bind combinator adds the local type to the discource. *)
  Definition bind {G D: Ctx} {t : Ty} (c : G |- t -| D) : G |- t -| D ;; t :=
    (fun k g => c (fun d x => k (d, x) x) g).

  (* If there is a dp available in the discourse G, 'he' selects the most recent one. 
   (This can be tweaked to account for features such as grammatical gender, number, etc ) *)

  (* A more general version of 'he', but for arbitrary types t. *)
  Definition retrieve {G} t i `{GetCtx G i t} : G |- t -| G :=
    (fun k g => k g (recall G i t g)).

  Definition he {G : Ctx} i `{GetCtx G i dp} : G |- dp -| G :=
    retrieve dp i.

  (* 'weak' weakens the discourse. You are allowed to grow the input, and shrink the output. *)
  Definition weak G D {G' D'} {t} `{Proj G G'} `{Proj D' D} (c : G' |- t -| D') : G |- t -| D :=
    (fun k g => c (fun d' x => k (proj d') x) (proj g)).

  Definition and : (s \ s) / s := fun x y => x /\ y.

  (* Capture takes a computation, and both 1) evaluates it; but 2) puts itself, unevaluated, onto the discourse *)
  Definition capture {G D} {t} (c : G |- t -| D) :
    G |- t -| D ;; (G |- t -| D) :=
    fun k g => c (fun d x => k (d, c) x) g.


  (* 'run' says that if you have a computation that returns another computation, you can extract the inner computation. 

   For example, consider "he is muddy", with type <> ;; dp |- s -| <>;; dp.

   If it is stored in a bigger context and recalled, 
     you have something of type (bigger context) |- (<> ;; dp |- s -| <> ;; dp) -| (same bigger context). This allows you to move from this double-computation to the inner computation. 


*)
  Definition run {G G1 D1 : Ctx} `{Proj G G1} {t} (c : G |- (G1 |- t -| D1) -| G) : G |- t -| D1.
    simpl in *.
    intros k g.
    refine (c _ g).
    intros d k2.
    apply (k2 k (proj g)).
  Defined.

  Parameter knows : (dp \ s) / s.

  (* Example: John knows he is muddy, and alice does too. *)

  (* John knows himself *)

  Definition john_knows_he_is_muddy : <> |- s -| <> ;; dp ;; (<> ;; dp |- dp \ s -| <> ;; dp) :=
    bind (lift john) <| capture (lift knows |> (he 0 <| lift (iv "muddy"))).

  (* In the covariant version, alice is bound, so alice fills in the dp hole in "knows (s)he is muddy " *)
  Eval compute in (lower (john_knows_he_is_muddy <| lift and |> (bind (lift alice) <| run (retrieve _ 1)))).
  (* knows (et "muddy" (e "alice")) (e "alice") /\ knows (et "muddy" (e "john")) (e "john") *)

  (* In the invariant version, we do not bind alice, so john is still the most recent dp. *)
  Eval compute in (lower (john_knows_he_is_muddy <| lift and |> ((lift alice) <| run (retrieve _ 0)))).
  (* knows (et "muddy" (e "john")) (e "alice") /\ knows (et "muddy" (e "john")) (e "john") *)

End Ling.
