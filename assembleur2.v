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
Require Import NPeano.
Fixpoint brem (n:nat) : bool :=
  if (beq_nat ((n/2)*2) n)
  then false
  else true.

(*
n: nat a encoder
SearchAbout()
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


(* ********************************************************************** *)
(*                              DECODE                                    *)
(* ********************************************************************** *)



Fixpoint decode (l : list bool) : (nat):=
  match l with
  | [] => 0
  | e::rest => match e with
         | false => decode rest
         | true => (decode rest) + (pow 2 ((length rest)))
         end
  end.


Compute (decode [false; true; true]).
Compute (decode [false;false;false;false;     false;true;false;true]).




