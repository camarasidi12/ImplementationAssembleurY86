Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Init.Nat.
Import ListNotations.
(*-------------------Representation-Binaire-------------------------------------*)
(*ou reecrire fonction mod2 pour rendre que true ou false*)
(*Fixpoint nat_to_bool (n:nat) : bool :=
  match (n mod 2) with
  |0 => false
  |1 => true
  |(S p) => false (*theoreme pour prouver que ce cas narrive jamais*)
  end.*)

Definition brem (n:nat) : bool :=
  if (beq_nat ((n/2)*2) n)
  then false
  else true.
(*
n: nat a encoder
k: encoder sur k bits
TODO: fonction decode : (list bool) -> nat
*)
Fixpoint encode (n:nat)(k:nat):(list bool):=
  match k with
  |0 => []
  |(S p) => (encode (n/2) p)++(brem n)::[]
  end.

Compute (encode 5 4).

(*-------------------Representation-Instructions--------------------------------*)
(*TODO:
-displacement: inter_code_car, eval_inter_code_car, instruction, decode_ins_icc
 *)

(*Representation dun code intermediaire qui va generer du binaire*)
Inductive inter_code_car : Type :=
|hexcar : nat -> inter_code_car (*generates 4-bit binary word*)
|constant: nat -> inter_code_car (*generates 4-bytes binary code*)
(*|displacement: nat -> inter_code_car*) (*generates 4-bytes binary code/ negative representation*)
.

(*evaluation of a inter_code_car*)
Fixpoint eval_inter_code_car (icc : inter_code_car) : (list bool) :=
  match icc with
  |(hexcar n) => (encode n 4)
  |(constant n) => (encode n 32)
  end.


(*hexadecimal is a list of inter_code_cars*)
(*Inductive type for register*)
(*1 register represented by 4 bits*)
Inductive reg: Type :=
|EAX: reg
|ECX: reg
|EDX: reg
|EBX: reg
|ESP: reg
|EBP: reg
|ESI: reg
|EDI: reg
|F : reg.


(*decode register*)
Fixpoint decode_reg (r : reg) : (list bool) :=
  match r with
  |EAX => (encode 0 4)
  |ECX => (encode 1 4)
  |EDX => (encode 2 4)
  |EBX => (encode 3 4)
  |ESP => (encode 4 4)
  |EBP => (encode 5 4)
  |ESI => (encode 6 4)
  |EDI => (encode 7 4)
  |F => (encode 15 4)
  end.


(*Operators represented by 1 byte*)
Inductive operator : Type :=
|ADD : operator
|SUB : operator
|AND : operator
|XOR : operator
.

(*decode operator to binary*)
Fixpoint decode_op (op: operator) : (list bool) :=
  match op with
  |ADD => (encode 6 4)++(encode 0 4)
  |SUB => (encode 6 4)++(encode 1 4)
  |AND => (encode 6 4)++(encode 2 4)
  |XOR => (encode 6 4)++(encode 3 4)
  end.

(*1 instruction represented by a maximum of 6 bytes*)
Inductive instruction: Type :=
|halt : instruction
|nop : instruction
|rrmovl : reg -> reg -> instruction
|irmovl : nat -> reg -> instruction
(*|rmmovl : reg -> constant -> reg -> instruction
|mrmovl : constant -> reg -> reg -> instruction*)
|opl : operator -> reg -> reg -> instruction
.


Fixpoint decode_ins (i : instruction) : (list bool) :=
  match i with
  |halt => (encode 0 4)++(encode 0 4)
  |nop => (encode 1 4)++(encode 0 4)
  |(rrmovl ra rb) => (encode 2 4)++(encode 0 4)++(decode_reg ra)++(decode_reg rb)
  |(irmovl n rb) => (encode 3 4)++(encode 0 4)++(encode 15 4)++(decode_reg rb)++(encode n 32)
  |(opl op ra rb) => (encode 6 4)++(decode_op op)++(decode_reg ra)++(decode_reg rb)
  end.

Compute (decode_ins halt).
Compute (decode_ins nop).
Compute (decode_ins (rrmovl EAX ECX)).
Compute (decode_ins (irmovl 15 EBX)).

Compute (encode 1 32).
(* ********************************************************************** *)
(*                              DECODE                                    *)
(* ********************************************************************** *)



Fixpoint decode (l : list bool) : nat:=
  match l with
  | [] => 0
  | e::rest => match e with
         | false => decode rest
         | true => (decode rest) + (pow 2 (length rest))
         end
  end.


Compute (decode [false; true; true]).
Compute (decode [false;false;false;false;     false;true;false;true]).
SearchAbout fst.
(* ********************************************************************** *)
(*                              LEMMA                                     *)
(* ********************************************************************** *)
(*case_eq a*)

(*lemme cas de base pour eq_decode_encode*)
Lemma eq_decode_encode_len1 : forall (b: bool),
    encode (decode [b]) 1 = [b].
Proof.
  intros.
  simpl.
  case b.
  -trivial.
  -trivial.
Qed.

(*TODO: delete lemma?*)
Lemma eq_decode_encode_len0: forall (l: list bool),
    encode (decode l) 0 = [].
Proof.
  intros. trivial.
  Qed.

SearchAbout (?X = ?Y <-> ?Y = ?X). (*Nat.eq_sym_iff*)
SearchAbout cons app.
Print concat.
SearchAbout cons.

(*correct with :
encode (decode b::l) (length b::l) = encode (decode l) (lenght l) ++ [b]
*)
Lemma bool_conc_list: forall (b:bool) (l: list bool),
    b::l = [b] ++ l.
Proof.
  intros.
  case b.
  -trivial.
  -trivial.
Qed.

Lemma eq_head: forall (b:bool) (l1 l2:list bool),
     b::l1 = b::l2 -> l1 = l2.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.

Fixpoint last_l (l: list bool) : list bool :=
  match l with
  |[] => []
  |a::[] => [a]
  |a::r => last_l r
  end.

(*Fixpoint first_l (l: list bool) : list bool :=
  match l with
  |[] => []
  |a::r => [a]
  end.*)

(*Fixpoint without_first (l: list bool) : list bool :=
  match l with
  |[] => []
  |a::r => r
  end.*)

Fixpoint without_last (l :list bool) : list bool :=
  match l with
  |[] => []
  |a::[] => []
  |a::r => a::without_last r
  end.

(*Fixpoint middle_l (l :list bool): list bool :=
  without_first (without_last l).*)

(*Lemma build_l: forall (l: list bool),
    l = (first_l l) ++ (middle_l l) ++ (last_l l).
Proof. Admitted.*)

(*TODO: show*)
Lemma same_l_2:
  forall (l: list bool),
    (without_last l) ++ (last_l l) = l.
Proof. Admitted.

(*TODO: show*)
Lemma without_last_len: forall(l: list bool) (n: nat),
   (S n) = (length l) -> n = (length (without_last l)).
Proof. Admitted.

SearchAbout length 0. (*length_zero_iff_nil*)

(*TODO: show*)
Lemma decode_div2_eq_without_last:
  forall (l: list bool),
    (decode l) / 2 = decode (without_last l).
Proof.
  intro.
  induction l.
  -trivial.
  -case a.
   +(*Opaque without_last.*)
    simpl.
    case l.
    *trivial.
    *simpl.
    Admitted.

SearchAbout beq_nat. (*beq_nat_true*)
SearchAbout Nat.divmod.


(*TODO: show*)
Lemma eq_add_2pow: forall (n k: nat),
    beq_nat (n/2 *2) n = beq_nat ((n+2^k)/2*2) (n+2^k).
Proof. Admitted.

Lemma brem_add_2pow: forall (n k: nat),
    k > 0 -> (brem n) = (brem (n + (pow 2 k))).
Proof.
  intros. unfold brem.
  case_eq (beq_nat (n/2 *2) n);intro heq.
  - rewrite <- eq_add_2pow.
    rewrite heq.
    reflexivity.
  - rewrite <- eq_add_2pow.
    rewrite heq.
    reflexivity.
Qed.  


Lemma same_last: forall (l: list bool) (b: bool),
    (length l) > 0 -> (last_l l) = (last_l (b::l)).
Proof.
  intro.
  induction l.
  - intros. inversion H.
  -intros.
   destruct l.
   +simpl. reflexivity.
   +apply IHl with (b:=b).
    inversion H. subst. auto.
Qed.
   

Lemma brem_decode_eq_last: forall (l: list bool),
    length l > 0 -> brem (decode l) :: [] = (last_l l).
Proof.
  intro l.
  induction l.
  -intro. inversion H.
  - intro.
    Opaque brem.
   Opaque last_l.
   case a.
    +simpl.
     destruct l.
     * simpl.
       reflexivity.
     * rewrite <- brem_add_2pow with (n:=(decode (b::l))) (k:=(length (b::l)));simpl;try omega.
       rewrite <- same_last;simpl;try omega.
       apply IHl.
       simpl. omega.
    +simpl.
     destruct l.
     * simpl.
       reflexivity.
     * rewrite <- same_last;try (simpl;omega).
       apply IHl.
       simpl;omega.
Qed.
   

Lemma singleton: forall (l : list bool),
    1 = (length l) -> exists b:bool, l = [b].
Proof.
  intros.
  induction l.
  -inversion H.
  -inversion H.
   case a.
   +exists true.
    apply Nat.eq_sym_iff in H1.
    apply length_zero_iff_nil in H1.
    rewrite H1.
    reflexivity.
   +exists false.
    apply Nat.eq_sym_iff in H1.
    apply length_zero_iff_nil in H1.
    rewrite H1.
    reflexivity.
Qed.
  

Print fst.
SearchAbout 0 gt.

Lemma eq_decode_encode_breakdown:
  forall (n:nat) (l:list bool),
    (S n) = (length l) ->
    (encode (decode l) (S n)) =
    (encode (decode (without_last l)) n) ++ (last_l l).
Proof.
  intros.
  induction n.
  -apply singleton in H.
   elim H.
   intros.
   rewrite H0.
   rewrite eq_decode_encode_len1.
   rewrite eq_decode_encode_len0.
   simpl.
   reflexivity.
  -Opaque decode.
   simpl.
   rewrite <- decode_div2_eq_without_last.
   rewrite brem_decode_eq_last.
   +simpl.
    reflexivity.
   +rewrite <- H. apply gt_Sn_O.
Qed.

Print length_zero_iff_nil.

Lemma eq_decode_encode: forall (n:nat) (l: list bool),
      n = (length l) -> (encode (decode l) n) = l.
  Proof.
    intro.
    induction n.
    -intros. apply Nat.eq_sym_iff in H.
     apply length_zero_iff_nil in H.
     rewrite H. simpl. reflexivity.
    -intros.
     rewrite eq_decode_encode_breakdown.
     +rewrite IHn with (l:=(without_last l)).
      *rewrite same_l_2.
       reflexivity.
      *apply without_last_len.
       assumption.
     +assumption.
  Qed.


