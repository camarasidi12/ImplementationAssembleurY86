Require Import List.
Require Import Bool.
Require Import Arith.
Require Import Init.


(*On supposera un bit comme une bool.
Encodage: Encodage d'un Nat->Byte
On encode les entier sur 32 bit
4:nat = 100 en binaire
*)


Fixpoint encode (n:nat):(list bool):=
    match n with
    |0=>[false]
    |1=>[true]
    |n =>match ( n mod 2) with
         |0=>encode((n / 2))::[false]
         |1=>encode((n / 2) - 1)::[true]
         end
    end.
    
  
  