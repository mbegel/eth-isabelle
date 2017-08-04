(*
   Copyright 2017 Myriam Begel

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

theory "HoareTripleForInstructions3"

imports "HoareTripleForInstructions"
"../attic/BasicBlocks"
"../EvmFacts"

begin
type_synonym pred = "(state_element set \<Rightarrow> bool)"

(* We define here the program logic for BLOCKSs *)
(* We start with Hoare triples valid for the execution of one instruction *)

(* We have to add more instructions here *)
definition iszero_stack :: "w256 \<Rightarrow> w256" where
"iszero_stack w = (if w = 0 then (word_of_int 1) else (word_of_int 0))"

fun arith_2_1_low:: "arith_inst \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256" where
 "arith_2_1_low MUL = (\<lambda> a b .  a * b) "
| "arith_2_1_low DIV =
	(\<lambda> a divisor .
		(if divisor =(((word_of_int 0) ::  256 word))
			then(((word_of_int 0) ::  256 word))
			else (\<lambda> i .  word_of_int ( i)) ((Word.uint a) div (Word.uint divisor))))"
| "arith_2_1_low MOD =
  (\<lambda> a divisor .  (if divisor =(((word_of_int 0) ::  256 word)) then(((word_of_int 0) ::  256 word)) else
            (\<lambda> i .  word_of_int ( i)) ((Word.uint a) mod (Word.uint divisor))))"
| "arith_2_1_low _ = (\<lambda> a b . 0)"

fun arith_2_1_verylow:: "arith_inst \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256" where
 "arith_2_1_verylow ADD = (\<lambda> a b .  a + b) "
| "arith_2_1_verylow SUB = (\<lambda> a b .  a - b) "
| "arith_2_1_verylow inst_GT =
	(\<lambda> a b .  if a > b then(((word_of_int 1) ::  256 word)) else(((word_of_int 0) ::  256 word)))"
| "arith_2_1_verylow inst_EQ =
	(\<lambda> a b .  if a = b then(((word_of_int 1) ::  256 word)) else(((word_of_int 0) ::  256 word)))"
| "arith_2_1_verylow inst_LT =
	(\<lambda> a b .  if b > a then(((word_of_int 1) ::  256 word)) else(((word_of_int 0) ::  256 word)))"
| "arith_2_1_verylow _ = (\<lambda> a b . 0)"

fun arith_3_1:: "arith_inst \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256" where
 "arith_3_1 ADDMOD =
		(\<lambda> a b divisor .
     (if divisor =(((word_of_int 0) ::  256 word)) then(((word_of_int 0) ::  256 word))
			else (\<lambda> i .  word_of_int ( i)) ((Word.uint a + Word.uint b) mod (Word.uint divisor))))"
| "arith_3_1 MULMOD =
		(\<lambda> a b divisor .
     (if divisor =(((word_of_int 0) ::  256 word)) then(((word_of_int 0) ::  256 word))
			else (\<lambda> i .  word_of_int ( i)) ((Word.uint a * Word.uint b) mod (Word.uint divisor))))"
| "arith_3_1 _ = (\<lambda> a b c . 0)"

inductive triple_inst_arith :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_arith_mul :
    "triple_inst_arith
      (\<langle> h \<le> 1022 \<and> Glow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith MUL)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (v*w) \<and>*
       gas_pred (g - Glow) \<and>* rest)"
| inst_arith_div :
    "triple_inst_arith
      (\<langle> h \<le> 1022 \<and> Glow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith DIV)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_2_1_low DIV v w) \<and>*
       gas_pred (g - Glow) \<and>* rest)"
| inst_arith_mod :
    "triple_inst_arith
      (\<langle> h \<le> 1022 \<and> Glow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith MOD)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_2_1_low MOD v w) \<and>*
       gas_pred (g - Glow) \<and>* rest)"
|  inst_arith_add :
    "triple_inst_arith
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith ADD)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_2_1_verylow ADD v w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_arith_sub :
    "triple_inst_arith
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith SUB)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_2_1_verylow SUB v w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_arith_gt :
    "triple_inst_arith
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith inst_GT)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_2_1_verylow inst_GT v w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_arith_eq :
    "triple_inst_arith
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith inst_EQ)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_2_1_verylow inst_EQ v w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_arith_lt :
    "triple_inst_arith
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith inst_LT)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_2_1_verylow inst_LT v w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_arith_addmod :
    "triple_inst_arith
      (\<langle> h \<le> 1021 \<and> Gmid \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc (Suc h))) \<and>* stack (Suc (Suc h)) u \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith ADDMOD)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_3_1 ADDMOD u v w) \<and>*
       gas_pred (g - Gmid) \<and>* rest)"
|  inst_arith_mulmod :
    "triple_inst_arith
      (\<langle> h \<le> 1021 \<and> Gmid \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc (Suc h))) \<and>* stack (Suc (Suc h)) u \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Arith MULMOD)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (arith_3_1 MULMOD u v w) \<and>*
       gas_pred (g - Gmid) \<and>* rest)"
| inst_iszero :
    "triple_inst_arith
      (\<langle> h \<le> 1023 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc h) \<and>* stack h w \<and>* gas_pred g \<and>* rest)
      (n, Arith ISZERO)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (iszero_stack w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"

fun bits_2_1_verylow:: "bits_inst \<Rightarrow> w256 \<Rightarrow> w256 \<Rightarrow> w256" where
 "bits_2_1_verylow BYTE = get_byte"
| "bits_2_1_verylow inst_AND = (\<lambda> a b .  a AND b)"
| "bits_2_1_verylow inst_OR = (\<lambda> a b .  a OR b)"
| "bits_2_1_verylow inst_XOR = (\<lambda> a b .  a XOR b)"
| "bits_2_1_verylow _ = (\<lambda> a b  . 0)"

inductive triple_inst_bits :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_bits_not :
    "triple_inst_bits
      (\<langle> h \<le> 1023 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc h) \<and>* stack h w \<and>* gas_pred g \<and>* rest)
      (n, Bits inst_NOT)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (NOT w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_bits_and :
    "triple_inst_bits
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Bits inst_AND)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (bits_2_1_verylow inst_AND v w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_bits_or :
    "triple_inst_bits
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Bits inst_OR)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (bits_2_1_verylow inst_OR v w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_bits_xor :
    "triple_inst_bits
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Bits inst_XOR)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (bits_2_1_verylow inst_XOR v w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"
|  inst_bits_byte :
    "triple_inst_bits
      (\<langle> h \<le> 1022 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc (Suc h)) \<and>* stack (Suc h) v \<and>* stack h w \<and>*
			 gas_pred g \<and>* rest)
      (n, Bits BYTE)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (bits_2_1_verylow BYTE v w) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"

inductive triple_inst_pc :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_jumpdest :
    "triple_inst_pc
      (\<langle> h \<le> 1024 \<and> Gjumpdest \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height h \<and>* gas_pred g \<and>* rest)
      (n, Pc JUMPDEST)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height h \<and>*
       gas_pred (g - Gjumpdest) \<and>* rest)"
| inst_instPC :
    "triple_inst_pc
      (\<langle> h \<le> 1023 \<and> Gbase \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height h \<and>* gas_pred g \<and>* rest)
      (n, Pc PC)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (word_of_int n) \<and>*
       gas_pred (g - Gbase) \<and>* rest)"

inductive triple_inst_stack :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_push_n :
    "triple_inst_stack
      (\<langle> h \<le> 1023 \<and> length lst > 0 \<and> 32 \<ge> length lst \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* program_counter n \<and>*
       memory_usage m \<and>* stack_height h \<and>*
       gas_pred g \<and>* rest)
      (n, Stack (PUSH_N lst))
      (program_counter (n + (1 + int (length lst))) \<and>*
       continuing \<and>* memory_usage m \<and>*
       stack_height (Suc h) \<and>* gas_pred (g - Gverylow) \<and>*
       stack h (word_rcat lst) \<and>* rest)"
| inst_pop :
    "triple_inst_stack
      (\<langle> h \<le> 1023 \<and> Gbase \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>*
       stack_height (Suc h) \<and>* stack h w \<and>* gas_pred g \<and>* rest)
      (n, Stack POP)
      (program_counter (n + 1) \<and>* continuing \<and>*
       memory_usage m \<and>* stack_height h \<and>*
       gas_pred (g - Gbase) \<and>* rest)"
| inst_calldataload :
    "triple_inst_stack
      (\<langle> h \<le> 1023 \<and> Gverylow \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* memory_usage m \<and>* program_counter n \<and>* data_lst 0 lst \<and>*
       stack_height (Suc h) \<and>* stack h u \<and>* gas_pred g \<and>* rest)
      (n, Stack CALLDATALOAD)
      (program_counter (n + 1) \<and>* continuing \<and>* data_lst 0 lst \<and>*
       memory_usage m \<and>* stack_height (Suc h) \<and>*
       stack h (read_word_from_bytes (unat u) lst) \<and>*
       gas_pred (g - Gverylow) \<and>* rest)"

inductive triple_inst_misc :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
 inst_stop :
    "triple_inst_misc
      (\<langle> h \<le> 1024 \<and> 0 \<le> g \<and> m \<ge> 0\<rangle> \<and>* continuing \<and>* memory_usage m \<and>*
       program_counter n \<and>* stack_height h \<and>* gas_pred g \<and>* rest)
      (n, Misc STOP)
      (stack_height h \<and>* not_continuing \<and>* memory_usage m \<and>*
       program_counter n \<and>* action (ContractReturn []) \<and>*
       gas_pred g \<and>* rest)"
|inst_return :
    "triple_inst_misc
     (\<langle> h \<le> 1022 \<and> m \<ge> 0 \<and> length lst = unat v \<and> (Cmem (M m u v) - Cmem m) \<le> g \<rangle> \<and>*
      continuing \<and>* memory_usage m \<and>* memory_range u lst \<and>*
      program_counter n \<and>* stack_height (Suc (Suc h)) \<and>* gas_pred g \<and>*
      stack (Suc h) u \<and>* stack h v \<and>* rest)
     (n, Misc RETURN)
     (stack_height (Suc (Suc h)) \<and>* not_continuing \<and>* memory_usage (M m u v) \<and>*
      action (ContractReturn lst) \<and>* gas_pred (g - (Cmem (M m u v) - Cmem m)) \<and>*
      stack (Suc h) u \<and>* stack h v \<and>* memory_range u lst \<and>*
      program_counter n \<and>* rest)"

definition memory :: "w256 \<Rightarrow> w256 \<Rightarrow> state_element set_pred" where
"memory ind w = memory_range ind (word_rsplit w)"

definition gcopy_aux :: "w256 \<Rightarrow> int" where
"gcopy_aux s = (Gcopy * (Word.uint s +( 31 :: int)) div( 32 :: int))"

definition w8_of_inst :: "inst \<Rightarrow> byte" where
"w8_of_inst inst =
    (case  index (inst_code inst)(( 0 :: nat)) of
      None =>(((word_of_int 0) ::  8 word))
    | Some a => a
    )"

definition code_range_minus_current_inst :: "int \<Rightarrow> inst list \<Rightarrow> int \<Rightarrow> state_element set \<Rightarrow> bool" where
"code_range_minus_current_inst src insts n = 
  (if src \<le> n \<and> n \<le> src + (sum_list (map inst_size insts))
    then code_range src (take (nat (n - src)) insts) \<and>* code_range (n+1) (drop (nat (n+1)) insts)
    else code_range src insts)"

inductive triple_inst_memory :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
 inst_mload :
    "triple_inst_memory
      (\<langle> h \<le> 1023  \<and> g \<ge> Gverylow - Cmem memu + Cmem (M memu memaddr 32) \<and> memu \<ge> 0 \<and>
        length (word_rsplit v::byte list) = unat (32::w256)\<rangle> \<and>*
       stack h memaddr \<and>* stack_height (h+1) \<and>* program_counter n \<and>*   
       memory_usage memu \<and>* memory memaddr v \<and>* gas_pred g \<and>* continuing \<and>* rest)
      (n, Memory MLOAD)
      (program_counter (n + 1) \<and>* stack_height (h + 1) \<and>* stack h v \<and>*
       memory memaddr v \<and>* memory_usage (M memu memaddr 32) \<and>*
       gas_pred (g - Gverylow + Cmem memu - Cmem (M memu memaddr 32)) \<and>*
       continuing \<and>* rest)"
| inst_mstore :
    "triple_inst_memory
      (\<langle> h \<le> 1022 \<and> g \<ge> Gverylow - Cmem memu + Cmem (M memu memaddr 32) \<and> memu \<ge> 0 \<and>
        length (word_rsplit old_v::byte list) = unat (32::w256) \<and>
        length (word_rsplit v::byte list) = unat (32::w256)\<rangle> \<and>*
       stack (h+1) memaddr \<and>* stack h v \<and>* stack_height (h+2) \<and>*
       program_counter n \<and>* memory_usage memu \<and>*
       memory memaddr old_v \<and>* gas_pred g \<and>* continuing \<and>* rest)
      (n, Memory MSTORE)
      (program_counter (n + 1) \<and>* stack_height h \<and>* memory memaddr v \<and>* 
       gas_pred (g - Gverylow + Cmem memu - Cmem (M memu memaddr 32)) \<and>*
       memory_usage (M memu memaddr 32) \<and>* continuing \<and>* rest)"
| inst_codecopy :
      "triple_inst_memory
        (\<langle>h \<le> 1021 \<and> g \<ge> Gverylow + gcopy_aux len \<and> m \<ge> 0 \<and> length lst = unat len \<and>
         length xs = (if nat m > unat dst_start + unat len then unat len else nat m - unat dst_start)\<rangle> \<and>*
         program_counter n \<and>* continuing \<and>* gas_pred g \<and>* stack_height (Suc (Suc (Suc h))) \<and>*
         stack h len \<and>* stack (Suc h) src_start \<and>* stack (Suc (Suc h)) dst_start \<and>*
         memory_range dst_start xs \<and>*
         code_range (uint dst_start) lst \<and>* memory_usage m \<and>* rest)
        (n, Memory CODECOPY)
        (program_counter (n+1) \<and>* continuing \<and>* gas_pred (g - Gverylow - gcopy_aux u) \<and>*
         stack_height h \<and>* memory_range dst_start (map w8_of_inst lst) \<and>*
         code_range (uint dst_start) lst \<and>* memory_usage m \<and>* rest)"

inductive triple_inst_info :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
 inst_callvalue:
    "triple_inst_info
      (\<langle> h \<le> 1023 \<and> Gbase \<le> g \<and> m \<ge> 0\<rangle> \<and>*
       continuing \<and>* program_counter n \<and>*
       memory_usage m \<and>* stack_height h \<and>* sent_value w \<and>*
       gas_pred g \<and>* rest)
      (n, Info CALLVALUE)
      (program_counter (n + 1) \<and>*
       continuing \<and>* memory_usage m \<and>* sent_value w \<and>*
       stack_height (Suc h) \<and>* gas_pred (g - Gbase) \<and>*
       stack h w \<and>* rest)"

definition new_log_entry :: "address \<Rightarrow> w256 list \<Rightarrow> byte list \<Rightarrow> log_entry"
where
"new_log_entry addr topics data = \<lparr>log_addr = addr, log_topics = topics, log_data = data \<rparr>"

inductive triple_inst_log :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
 inst_log0:
    "triple_inst_log
    (\<langle>h\<le> 1022 \<and> g \<ge> (Glog + Glogdata * (uint u)) \<and> m \<ge> 0 \<and> length lst = unat u\<rangle> \<and>*
     program_counter n \<and>* gas_pred g \<and>* memory_usage m \<and>* memory_range v lst \<and>*
     stack h u \<and>* stack (Suc h) v \<and>* stack_height (Suc (Suc h)) \<and>*
     log_number l \<and>* continuing \<and>* this_account addr \<and>* rest)
    (n, Log LOG0)
    (program_counter (n+1) \<and>* gas_pred (g - (Glog + Glogdata * (uint u))) \<and>* memory_usage m \<and>*
     stack_height h \<and>* log_number (Suc l) \<and>* logged l (new_log_entry addr [] lst) \<and>*
     memory_range v lst \<and>* continuing \<and>* this_account addr \<and>* rest)"

inductive triple_inst :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_arith :
    "triple_inst_arith p (n, Arith i) q \<Longrightarrow> triple_inst p (n, Arith i) q"
| inst_bits :
    "triple_inst_bits p (n, Bits i) q \<Longrightarrow> triple_inst p (n, Bits i) q"
| inst_info :
    "triple_inst_info p (n, Info i) q \<Longrightarrow> triple_inst p (n, Info i) q"
| inst_log :
    "triple_inst_log p (n, Log i) q \<Longrightarrow> triple_inst p (n, Log i) q"
| inst_memory :
    "triple_inst_memory p (n, Memory i) q \<Longrightarrow> triple_inst p (n, Memory i) q"
| inst_misc :
    "triple_inst_misc p (n, Misc i) q \<Longrightarrow> triple_inst p (n, Misc i) q"
| inst_pc :
    "triple_inst_pc p (n, Pc i) q \<Longrightarrow> triple_inst p (n, Pc i) q"
| inst_stack :
    "triple_inst_stack p (n, Stack i) q \<Longrightarrow> triple_inst p (n, Stack i) q"
| inst_swap :
		"triple_inst
			(\<langle> h \<le> 1023 \<and> Suc (unat n) \<le> h \<and> g \<ge> Gverylow \<and> m \<ge> 0\<rangle> \<and>*
			 stack_height (Suc h) \<and>* stack h w \<and>* stack (h - (unat n) - 1) v \<and>*
			 program_counter k \<and>* gas_pred g \<and>* memory_usage m \<and>*
			 continuing \<and>* rest)
			(k, Swap n)
			(program_counter (k + 1) \<and>* gas_pred (g - Gverylow) \<and>*
			 stack_height (Suc h) \<and>* stack h v \<and>* stack (h - (unat n) - 1) w \<and>*
			 memory_usage m \<and>* continuing \<and>* rest)"
| inst_dup :
    "triple_inst
      (\<langle> h \<le> 1023 \<and> unat n < h \<and> g \<ge> Gverylow\<rangle> \<and>*
       stack_height h \<and>* stack (h - (unat n) - 1) w \<and>*
       memory_usage m \<and>* program_counter k \<and>*
       gas_pred g \<and>* continuing \<and>* rest )
      (k, Dup n)
      (program_counter (k + 1) \<and>* gas_pred (g - Gverylow) \<and>*
       stack_height (Suc h) \<and>* stack (h - (unat n) - 1) w \<and>* stack h w \<and>*
       memory_usage m \<and>* continuing \<and>* rest )"
| inst_strengthen_pre:
    "triple_inst p i q \<Longrightarrow> (\<And>s. r s \<Longrightarrow> p s) \<Longrightarrow> triple_inst r i q"
| inst_false_pre:
    "triple_inst \<langle>False\<rangle> i post"
end
