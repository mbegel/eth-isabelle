(*
   Copyright 2016 Yoichi Hirai

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

theory ContractSem

imports Main "~~/src/HOL/Word/Word" "./lem/Evm"
(* If ./lem/Evm is missing, try executing `make lem-thy` *)

begin

  
(* Generated by Lem in EvmAuxiliary.thy *)
(* termination cut_natural_map by lexicographic_order
*)
(*
termination store_byte_list_memory by lexicographic_order *)

termination log256floor by lexicographic_order

termination word_exp by lexicographic_order


declare
  rotl64_def [simp]
  big_def [simp]
  keccakf_randc_def [simp]
  keccakf_rotc_def [simp]
  keccakf_piln_def [simp]
  get_def [simp]
  get_n_def [simp]
  setf_def [simp]
  theta_t_def [simp]
  theta_def [simp]
  rho_pi_inner_def [simp]
  rho_pi_changes_def [simp]
  rho_pi_def [simp]
  chi_for_j_def [simp]
  filterI_def [simp]
  chi_def [simp]
  iota_def [simp]
  for_inner_def [simp]
  keccakf_rounds_def [simp]
  word_rsplit_aux.psimps [simp]
(*  word64FromBoollist.psimps [simp] *)
  word_rcat_def [simp]
  invert_endian_def [simp]
  keccakf_def [simp]
  mdlen_def [simp]
  rsiz_def [simp]
  word8_to_word64_def [simp]
  update_byte_def [simp]
  sha3_update.psimps [simp]
  keccak_final_def [simp]
  initial_st_def [simp]
  initial_pos_def [simp]
  list_fill_right_def [simp]
  keccak'_def [simp]
  

  
declare vctx_advance_pc_def [simp]
declare vctx_next_instruction_def [simp]
declare call_def [simp]

text {* When the if-condition is known to be True, the simplifier can
proceed into the then-clause.  The \textit{simp} attribute encourages the simplifier
to use this equation from left to right whenever applicable.  *}
lemma strict_if_True [simp] :
"strict_if True a b = a True"
apply(simp add: strict_if_def)
done

text {* When the if-condition is known to be False, the simplifier
can proceed into the else-clause. *}
lemma strict_if_False [simp] :
"strict_if False a b = b True"
apply(simp add: strict_if_def)
done

text {* When the if-condition is not known to be either True or False,
the simplifier is allowed to perform computation on the if-condition.
The \textit{cong} attribute tells the simplifier to try to rewrite the
left hand side of the conclusion, using the assumption.
*}
lemma strict_if_cong [cong] :
"b0 = b1 \<Longrightarrow> strict_if b0 x y = strict_if b1 x y"
apply(auto)
done

declare empty_program_def [simp]
declare prepend_annotation_def [simp]
declare program_annotation_of_lst.simps [simp]
declare program_of_lst_def [simp]
   
subsection {* The Result of an Instruction *}

declare instruction_failure_result_def [simp]

text {* When the contract returns, the result of the instruction always looks like this: *}
  
declare instruction_return_result_def [simp]
declare M_def [simp]
declare update_balance_def [simp]
declare vctx_update_storage_def [simp]
declare stack_0_0_op_def [simp]
declare stack_0_1_op_def [simp]
declare stack_1_1_op_def [simp]
declare stack_2_1_op_def [simp]
declare stack_3_1_op_def [simp]
declare sstore_def [simp]
declare build_aenv_def [simp]
declare jump_def [simp]

text {* When the second argument is already @{term True}, the simplification can continue.
Otherwise, the Isabelle/HOL simplifier is not allowed to expand the definition of
@{term blockedInstructionContinue}. *}
lemma unblockInstructionContinue [simp] :
"blockedInstructionContinue v True = InstructionContinue v"
apply(simp add: blockedInstructionContinue_def)
done

text {* This is another reminiscent of my struggle against the Isabelle/HOL simplifier.
Again, the simplifier is not allowed to expand the definition unless the second argument
is known to be @{term True}.*}

lemma unblock_jump [simp]:
"blocked_jump v c True = jump v c"
apply(simp add: blocked_jump_def)
done

declare jumpi_def [simp]
declare datasize_def [simp]
declare read_word_from_bytes_def [simp]
declare cut_data_def [simp]
declare delegatecall_def [simp]
declare callcode_def [simp]
declare create_def [simp]
declare ret_def [simp]
declare stop_def [simp]
declare pop_def [simp]
(* declare store_byte_list_memory.psimps [simp] *)
declare store_word_memory_def [simp]
declare mstore_def [simp]
declare mload_def [simp]
declare mstore8_def [simp]
declare calldatacopy_def [simp]
declare codecopy_def [simp]
declare extcodecopy_def [simp]
declare pc_def [simp]
declare log_def [simp]

declare list_swap_def [simp]

text "For testing, I prove some lemmata:"
lemma "list_swap 1 [0, 1] = Some [1, 0]"
apply(auto)
done

lemma "list_swap 2 [0, 1] = None"
apply(auto)
done

lemma "list_swap 2 [0, 1, 2] = Some [2, 1, 0]"
apply(auto)
done

lemma "list_swap 3 [0, 1, 2, 3] = Some [3, 1, 2, 0]"
apply(auto)
done

lemma"list_swap 1 [0, 1, 2, 3] = Some [1, 0, 2, 3]"
apply(auto)
done

declare swap_def [simp]

declare general_dup_def [simp]
declare suicide_def [simp]

lemma "Word.word_rcat [(0x01 :: byte), 0x02] = (0x0102 :: w256)"
apply(simp only: Word.word_rcat_def)
apply(simp add: bin_rcat_def)
apply(simp add: bin_cat_def)
done

declare instruction_sem_def [simp]

declare check_annotations_def [simp]
declare next_state_def [simp]
declare program_sem.simps [simp]


declare build_vctx_called.simps [simp]

declare build_cctx_def [simp]

declare is_call_like_def [simp]

declare build_vctx_returned.simps [simp]

declare build_vctx_failed_def [simp]

declare account_state_pop_ongoing_call_def [simp]

declare empty_account_def [simp]

text {* The following lemmata regulates the Isabelle simplifier so that the definition of
update\_account\_state is only sometimes expanded.  *}

lemma update_account_state_None [simp] :
"update_account_state prev act v None =
   (let st = ((case  act of ContractFail _ =>(vctx_storage_at_call v) | _ =>(vctx_storage v) )) in
   (let bal = ((case  act of ContractFail _ =>(vctx_balance_at_call v) | _ =>(vctx_balance v) )) in
   (prev \<lparr>
     account_storage := st,
     account_balance :=
       (case act of ContractFail _ \<Rightarrow> account_balance prev
                 |  _ \<Rightarrow> bal (account_address prev)),
     account_ongoing_calls := account_ongoing_calls prev,
     account_killed :=
       (case act of ContractSuicide _ \<Rightarrow> True
                  | _ \<Rightarrow> account_killed prev) \<rparr>)))"
apply(case_tac act; simp add: update_account_state_def)
done

lemma update_account_state_Some [simp] :
"update_account_state prev act v (Some pushed) =
   (let st = ((case  act of ContractFail _ =>(vctx_storage_at_call v) | _ =>(vctx_storage v) )) in
   (let bal = ((case  act of ContractFail _ =>(vctx_balance_at_call v) | _ =>(vctx_balance v) )) in
   (prev \<lparr>
     account_storage := st,
     account_balance :=
       (case act of ContractFail _ \<Rightarrow> account_balance prev
                  |  _ \<Rightarrow> bal (account_address prev)),
     account_ongoing_calls := (v, pushed) # account_ongoing_calls prev,
     account_killed :=
       (case act of ContractSuicide _ \<Rightarrow> True
                  | _ \<Rightarrow> account_killed prev)\<rparr>)))"
apply(case_tac act; simp add: update_account_state_def)
done

lemma word_rcat_constant [simp] :
"word_rcat (constant_mark lst) = of_bl (List.concat (map to_bl lst))"
apply(simp only: word_rcat_bl)
apply(simp only: constant_mark_def)
done

declare unat_def [simp]
        maybe_to_list.simps [simp]
        vctx_pop_stack_def [simp]
        of_bl_def [simp]
        to_bl_def [simp]
        bl_to_bin_def [simp]

lemma iszero_iszero [simp] :
"((if b then (word_of_int 1 :: 256 word) else word_of_int 0) = 0) = (\<not> b) "
apply(auto)
done

lemma iszero_isone [simp] :
"((if b then (word_of_int 1 :: 256 word) else word_of_int 0) = 1) = b "
apply(auto)
done

declare Gzero_def [simp]
        Gbase_def [simp]
        Gverylow_def [simp]
        Glow_def [simp]
        Gmid_def [simp]
        Ghigh_def [simp]
        Gextcode_def [simp]
        Gbalance_def [simp]
        Gsload_def [simp]
        Gjumpdest_def [simp]
        Gsset_def [simp]
        Gsreset_def [simp]
        Rsclear_def [simp]
        Rsuicide_def [simp]
        Gsuicide_def [simp]
        Gcreate_def [simp]
        Gcodedeposit_def [simp]
        Gcall_def [simp]
        Gcallvalue_def [simp]
        Gcallstipend_def [simp]
        Gnewaccount_def [simp]
        Gexp_def [simp]
        Gexpbyte_def [simp]
        Gmemory_def [simp]
        Gtxcreate_def [simp]
        Gtxdatazero_def [simp]
        Gtxdatanonzero_def [simp]
        Gtransaction_def [simp]
        Glog_def [simp]
        Glogdata_def [simp]
        Glogtopic_def [simp]
        Gsha3_def [simp]
        Gsha3word_def [simp]
        Gcopy_def [simp]
        Gblockhash_def [simp]
        log256floor.psimps [simp]
        new_memory_consumption.simps [simp]
        meter_gas_def [simp]
        C_def [simp]
        Cmem_def [simp]
        Cextra_def [simp]
        L_def [simp]
        Ccallgas_def [simp]
        Ccall_def [simp]
        thirdComponentOfC_def [simp]
        vctx_next_instruction_default_def [simp]
        vctx_recipient_def [simp]
        vctx_stack_default_def [simp]
        subtract_gas.simps [simp]
        constant_mark_def [simp]
        bin_rcat_def [simp]
        
declare bits_inst_code.simps [simp]
declare sarith_inst_code.simps [simp]
declare arith_inst_code.simps [simp]
declare info_inst_code.simps [simp]
declare dup_inst_code_def [simp]
declare memory_inst_code.simps [simp]
declare storage_inst_code.simps [simp]
declare pc_inst_code.simps [simp]
declare stack_inst_code.simps [simp]
declare swap_inst_code_def [simp]
declare log_inst_code.simps [simp]
declare misc_inst_code.simps [simp]
declare inst_code.simps [simp]
declare inst_size_def [simp]

(*
| ProgramStepRunOut of variable_ctx (* the artificial step counter has run out *)
| ProgramToEnvironment of contract_action * storage * (address -> w256) * list w256 * list log_entry
   * maybe (variable_ctx * integer * integer)
  (** the program stopped execution because an instruction wants to talk to the environment
  for example because the execution returned, failed, or called an account.
  *)
| ProgramInvalid (* an unknown instruction is found.  Maybe this should just count as
  a failing execution *)

| ProgramAnnotationFailure (* an annotation turned out to be false.  This does not happen
  in reality, but this case exists for the sake of the verification. *)

| ProgramInit of call_env
*)

lemma program_sem_to_environment [simp]: "program_sem k con n net (InstructionToEnvironment a b c) = InstructionToEnvironment a b c"
apply(induct_tac n; auto)
done

lemma program_sem_annotation_failure [simp] : "program_sem k con n net InstructionAnnotationFailure = InstructionAnnotationFailure"
by (induct_tac n; auto)

lemma not_at_least_one :
  "\<not> 1 \<le> (aa :: 256 word) \<Longrightarrow> aa = 0"
apply(simp add:linorder_class.not_le)
done

lemma unat_suc : "unat (aa :: w256) = Suc n \<Longrightarrow> unat (aa - 1) = n"
apply(case_tac "aa \<ge> 1")
 apply(simp add: uint_minus_simple_alt)
apply(drule not_at_least_one)
apply(simp)
done

(* unat (1 + (aa - 1)) = Suc (unat(aa - 1)) *)

(*
lemma cut_memory_dom_nat :
  "\<forall> a aa b. unat aa = n \<longrightarrow> cut_memory_dom (a, aa, b)"
apply(induction n)
 apply(clarify)
 apply(rule cut_memory.domintros)
 apply(simp add: unat_eq_0 uint_0_iff)
apply(clarify)
apply(rule cut_memory.domintros)
apply(drule unat_suc)
apply(auto)
done

termination cut_memory
apply(auto simp add: cut_memory_dom_nat)
done
*)

end
