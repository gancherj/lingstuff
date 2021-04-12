
Require Import String. Import StringSyntax.
Require Import Ling.BS. Import BarkerShan.

(**** Some experimentation with gaps, covariant readings  *****)
(*** Everything below here is pretty experimental ***)


(* Gap is defined for all input and output categories *)
Definition gap {a b : Cat} : (a \\ b) || b -- a := fun x => x.

(* Simple gaps *)
Eval compute in (lower (lift john |> (lift loves <| gap))).


(* Ari knows he is muddy and Ben knows this *)

(* muddy, copulatives *)

Definition muddy : AP := baseAdj "muddy".
Definition is : (DP \ S) / AP := fun x y => x y.
Eval compute in (lower (lift john |> (lift is <| lift muddy))).

Definition knows : ((DP \ S) / S) := (Knows : (DP \ S) / S).

Check (bind (lift john) |> (lift knows <| (he |> (lift is <| lift muddy)))).

(* Anaphor for single props *)
Definition this : (S >> S) || S -- S := fun k => k.

(* Assumes a topic DP and a proposition P with a hole in it for a DP. Applies
   P to the topic. *)
Definition this2 : (DP >> ((DP >> S) >> S)) || S -- S.
  simpl.
  refine (fun k e p => k (p e)).
Defined.

(* Generalized bind *)
Definition gbind {a b c : Cat} (x : a || b -- c) : a || (c >> b) -- c :=
  fun k => x (fun e => k e e).

Check (bind (lift mary) |> (lift knows <| this2)).
Check (gbind (lift ((lower (he |> (lift is <| lift muddy)))))).

(* This pull combinator is kind of suspect. Maybe I can fix it with gaps *)
Definition pull {a b c d : Cat} (x : a || b -- (c >> d)) : (c >> a) || b -- d :=
  fun k z => x (fun f => k (f z)).

Definition ari : DP := baseE "ari".
Definition ben : DP := baseE "ben".

Check ((lower (he |> (lift is <| lift muddy)))).
Definition ari_knows_he_is_muddy : S || (DP >> S) >> S -- S := (bind (lift ari) |> (lift knows <| (pull (gbind (lift ((lower (he |> (lift is <| lift muddy))))))))).

Definition doesnt_know : ((DP \ S) / S) := fun x k => ~ (Knows x k).

Definition ben_doesnt_know_this : ((DP >> S) >> S) || S -- S :=
  (bind (lift ben) |> (lift doesnt_know <| this2)).
  
Eval compute in (lower (ari_knows_he_is_muddy |> (lift and <| ben_doesnt_know_this))).
