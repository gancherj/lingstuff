Require Import String.
Import StringSyntax.
Require Import List.

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
  

  Inductive Ty :=
  | DP | S | ArrL : Ty -> Ty -> Ty
  | ArrR : Ty -> Ty -> Ty
  | Comp : Ctx -> Ty -> Ctx -> Ty
  with
    Ctx := | Empty | Cons : Ctx -> Ty -> Ctx.

  Fixpoint interpTy (t : Ty) :=
    match t with
    | DP => E
    | S => Prop
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

  Parameter (alt : Prop -> ((interpTy DP) -> Prop) -> (interpTy DP) -> Prop).


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

  (* This second one, Recall, selects a type from a given discourse, using the most recent one available. *)
  Class Recall (G : Ctx) (t : Ty) := recall : G -> t.
  Instance Recall_here G t : Recall (G ;; t) t := fun g => snd g.
  Instance Recall_there G t1 t2 `{Recall G t1} : Recall (G ;; t2) t1 := fun g => recall (fst g).

  Definition lift {t : Ty} {G : Ctx} (x : t) : G |- t -| G := 
    fun k g => k g x.

  (* You can lower and evaluate any sentence that doesn't have any free variables in it. *)
  Definition lower {D} (c : <> |- S -| D): S :=
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




  Definition tv s : (DP \ S) / DP := eet s.
  Definition iv s : DP \ S := et s.

  Definition everyone {G : Ctx} : G |- DP -| G :=
    fun k g => forall x, k g x. 

  Definition someone {G : Ctx} : G |- DP -| G;;DP :=
    fun k g => exists x, k (g, x) x. 

  Definition everyone_sleeps : <> |- S -| <> :=
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

  Definition dp s : DP := e s.
  Definition john := dp "john".
  Definition alice := dp "alice".


  (* The bind combinator adds the local type to the discource. *)
  Definition bind {G D: Ctx} {t : Ty} (c : G |- t -| D) : G |- t -| D ;; t :=
    (fun k g => c (fun d x => k (d, x) x) g).

  (* If there is a DP available in the discourse G, 'he' selects the most recent one. 
   (This can be tweaked to account for features such as grammatical gender, number, etc ) *)
  Definition he {G : Ctx} `{Recall G DP} : G |- DP -| G :=
    (fun k g => k g (recall g)).

  (* 'weak' weakens the discourse. You are allowed to grow the input, and shrink the output. *)
  Definition weak G D {G' D'} {t} `{Proj G G'} `{Proj D' D} (c : G' |- t -| D') : G |- t -| D :=
    (fun k g => c (fun d' x => k (proj d') x) (proj g)).

  Definition and : (S \ S) / S := fun x y => x /\ y.

  (* Capture takes a computation, and both 1) evaluates it; but 2) puts itself, unevaluated, onto the discourse *)
  Definition capture {G D} {t} (c : G |- t -| D) :
    G |- t -| D ;; (G |- t -| D) :=
    fun k g => c (fun d x => k (d, c) x) g.

  (* A more general version of 'he', but for arbitrary types t. *)
  Definition retrieve {G} t `{Recall G t} : G |- t -| G :=
    fun k g => k g (recall g).

  (* 'run' says that if you have a computation that returns another computation, you can extract the inner computation. 

   For example, consider "he is muddy", with type <> ;; DP |- S -| <>;; DP.

   If it is stored in a bigger context and recalled, 
     you have something of type (bigger context) |- (<> ;; DP |- S -| <> ;; DP) -| (same bigger context). This allows you to move from this double-computation to the inner computation. 


*)
  Definition run {G G1 D1 : Ctx} `{Proj G G1} {t} (c : G |- (G1 |- t -| D1) -| G) : G |- t -| D1.
    simpl in *.
    intros k g.
    refine (c _ g).
    intros d k2.
    apply (k2 k (proj g)).
  Defined.

  (* Example: John knows himself, and alice does too. *)

  (* John knows himself *)

  Definition john_knows_himself : <> |- S -| <> ;; DP ;; (<> ;; DP |- DP \ S -| <> ;; DP) :=
    bind (lift john) <| capture (lift (tv "knows") |> he).

  (* In the covariant version, alice is bound, so alice fills in the DP hole in "knows (her)self" *)
  Eval compute in (lower (john_knows_himself <| lift and |> (bind (lift alice) <| run (retrieve _)))).
  (* eet "knows" (e "alice") (e "alice") /\ eet "knows" (e "john") (e "john") *)

  (* In the invariant version, we do not bind alice, so john is still the most recent DP. *)
  Eval compute in (lower (john_knows_himself <| lift and |> ((lift alice) <| run (retrieve _)))).
  (* eet "knows" (e "john") (e "alice") /\ eet "knows" (e "john") (e "john") *)

End Ling.
