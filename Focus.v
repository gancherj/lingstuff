
Require Import String. Import StringSyntax.
From Ling Require Import BS.
Import Ling.

Notation "x [ y ]" := (Focus y x) (at level 30, format "x [ y ]").

(* BOUGHT : capture the continuation, return the continuation along with the word *)

(* This version of focus doesn't work for phrases. Like 
    "I only GAVE IT TO MARY"
   meaning
     the only thing I did is "give it to mary"
    
   but maybe this is ok
*)
Definition focus {a b : Cat} (x : b) : a[b] || a -- b := fun (k : b -> a) => (x, k).


Definition only {c d : Cat} : S || S[c] -- (d / d) :=
  fun F => let '(x, k) := F id in forall z, k z -> z = x.

(* John bought lunch. *)
Check john.
Definition bought := mkTV "bought".
Definition lunch : DP := Ec "lunch".
Eval compute in (john <: (bought :> lunch)).

Eval compute in (lower (lift john <| (lift bought |> lift lunch))).

(* John only BOUGHT lunch *)

Eval compute in (lower (lift john <| ((only |> focus bought) |> lift lunch))).

(* John only bought LUNCH *)

Eval compute in (lower (lift john <| (only |> lift bought |> focus lunch))).

(* only can be moved around: John bought only LUNCH *)

Eval compute in (lower (lift john <| (lift bought |> (only |> focus lunch)))).

(* Currently "JOHN only bought lunch" doesn't work, since only is to the right of JOHN *)


(* only JOHN bought lunch *)

Eval compute in (lower ((only |> focus john) <| (lift bought |> lift lunch))).



(* prop anaphora with focussing *)

Definition unfocus {a b c d : Cat} (x : a || b -- (c[d])) : a || b -- c .
  refine (fmap _ x).
  apply (fun '(b, a) => a b).
Defined.
                                                              
Definition did_as_well : (S[DP] >> S) || S -- (DP \ S) :=
  (fun k '(_, f) => k (fun x => f x)).

Definition gbind {a b c : Cat} (x : a || b -- c) : a || (c >> b) -- c :=
  fun k => x (fun e => k e e).

Definition reset {a c : Cat} (x : a || S -- S) : c || c -- a := lift (lower x).


(* We focus john, and evaluate the first sentence. We call gbind on this, and then consider only the ordinary semantics of the first sentence. *)
Check (unfocus (gbind (reset (focus john <| (lift bought |> lift lunch))))).
   

(* Thus we now have a referent of type S[DP]. This can be fed into did_as_well. *)
Eval compute in (lower ((unfocus (gbind (reset (focus john <| (lift bought |> lift lunch)))))
         <|
         (lift and |>
               (lift mary <| did_as_well)))).
