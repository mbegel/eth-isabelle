theory Escrow

imports
  Dispatcher
begin
(*
pragma solidity ^0.4.0;
contract EscrowWallet {

    address from;
    address to;
    address owner;

    function EscrowWallet(address _from, address _to) public {
            from = _from;
            to = _to;
            owner = msg.sender;
    }

    function addfund() payable public  {
        require (msg.sender == from);
    }

    function refund() public {
        require (msg.sender == owner);
        selfdestruct(from);
    }

    function pay() public {
        require (msg.sender == owner);
        selfdestruct(to);
    }
}

Compiled with:
 solc --optimize --overwrite -o escrow --bin-runtime --asm --hashes escrow.sol

8f9595d4: addfund()
1b9265b8: pay()
590e1ae3: refund()


*)
value"(parse_bytecode ''6060604052600436106100565763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416631b9265b8811461005b578063590e1ae3146100705780638f9595d414610083575b600080fd5b341561006657600080fd5b61006e61008b565b005b341561007b57600080fd5b61006e6100ce565b61006e610111565b6002543373ffffffffffffffffffffffffffffffffffffffff9081169116146100b357600080fd5b60015473ffffffffffffffffffffffffffffffffffffffff16ff5b6002543373ffffffffffffffffffffffffffffffffffffffff9081169116146100f657600080fd5b60005473ffffffffffffffffffffffffffffffffffffffff16ff5b6000543373ffffffffffffffffffffffffffffffffffffffff90811691161461013957600080fd5b5600a165627a7a723058207bd2ee8051b098c799df41466599cd311e376fd36372f2becec08fe494ba3cc10029'')"

definition insts_ex where
"insts_ex == [Stack (PUSH_N [0x60]), Stack (PUSH_N [0x40]), Memory MSTORE, Stack (PUSH_N [4]), Info CALLDATASIZE,
  Arith inst_LT, Stack (PUSH_N [0, 0x56]), Pc JUMPI, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]),
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Stack (PUSH_N [0]), Stack CALLDATALOAD, Arith DIV, Bits inst_AND, Stack (PUSH_N [0x1B, 0x92, 0x65, 0xB8]),
  Dup 1, Arith inst_EQ, Stack (PUSH_N [0, 0x5B]), Pc JUMPI, Dup 0, Stack (PUSH_N [0x59, 0xE, 0x1A, 0xE3]),
  Arith inst_EQ, Stack (PUSH_N [0, 0x70]), Pc JUMPI, Dup 0, Stack (PUSH_N [0x8F, 0x95, 0x95, 0xD4]),
  Arith inst_EQ, Stack (PUSH_N [0, 0x83]), Pc JUMPI, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD,
  Pc JUMPDEST, Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [0, 0x66]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0,
  Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0, 0x6E]), Stack (PUSH_N [0, 0x8B]), Pc JUMP, Pc JUMPDEST,
  Misc STOP, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [0, 0x7B]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0, 0x6E]), Stack (PUSH_N [0, 0xCE]),
  Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0, 0x6E]), Stack (PUSH_N [1, 0x11]), Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [2]), Storage SLOAD, Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Stack (PUSH_N [0, 0xB3]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [1]), Storage SLOAD,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [2]), Storage SLOAD, Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Stack (PUSH_N [0, 0xF6]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0]), Storage SLOAD,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Misc SUICIDE, Pc JUMPDEST, Stack (PUSH_N [0]), Storage SLOAD, Info CALLER,
  Stack (PUSH_N
          [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
           0xFF, 0xFF, 0xFF, 0xFF]),
  Swap 0, Dup 1, Bits inst_AND, Swap 1, Bits inst_AND, Arith inst_EQ, Stack (PUSH_N [1, 0x39]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58]), Arith SHA3,
  Stack (PUSH_N
          [0xD2, 0xEE, 0x80, 0x51, 0xB0, 0x98, 0xC7, 0x99, 0xDF, 0x41, 0x46, 0x65, 0x99, 0xCD, 0x31, 0x1E,
           0x37, 0x6F, 0xD3, 0x63, 0x72, 0xF2, 0xBE, 0xCE, 0xC0, 0x8F, 0xE4, 0x94]),
  Unknown 0xBA, Memory EXTCODECOPY, Unknown 0xC1, Misc STOP, Unknown 0x29]"
(* 135 instructions *)

lemma
 "parse_bytecode ''6060604052600436106100565763ffffffff7c01000000000000000000000000000000000000000000000000000000006000350416631b9265b8811461005b578063590e1ae3146100705780638f9595d414610083575b600080fd5b341561006657600080fd5b61006e61008b565b005b341561007b57600080fd5b61006e6100ce565b61006e610111565b6002543373ffffffffffffffffffffffffffffffffffffffff9081169116146100b357600080fd5b60015473ffffffffffffffffffffffffffffffffffffffff16ff5b6002543373ffffffffffffffffffffffffffffffffffffffff9081169116146100f657600080fd5b60005473ffffffffffffffffffffffffffffffffffffffff16ff5b6000543373ffffffffffffffffffffffffffffffffffffffff90811691161461013957600080fd5b5600a165627a7a723058207bd2ee8051b098c799df41466599cd311e376fd36372f2becec08fe494ba3cc10029'' = insts_ex"
  unfolding insts_ex_def
  by eval

definition "blocks_escrow == build_blocks insts_ex"

lemma blocks_escrow_simp:
 "blocks_escrow = [(0, [(0, Stack (PUSH_N [0x60])), (2, Stack (PUSH_N [0x40])), (4, Memory MSTORE), (5, Stack (PUSH_N [4])),
       (7, Info CALLDATASIZE), (8, Arith inst_LT), (9, Stack (PUSH_N [0, 0x56]))],
   Jumpi),
  (13, [(13, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])),
        (18, Stack (PUSH_N
                     [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0])),
        (48, Stack (PUSH_N [0])), (50, Stack CALLDATALOAD), (51, Arith DIV), (52, Bits inst_AND),
        (53, Stack (PUSH_N [0x1B, 0x92, 0x65, 0xB8])), (58, Dup 1), (59, Arith inst_EQ),
        (60, Stack (PUSH_N [0, 0x5B]))],
   Jumpi),
  (64, [(64, Dup 0), (65, Stack (PUSH_N [0x59, 0xE, 0x1A, 0xE3])), (70, Arith inst_EQ),
        (71, Stack (PUSH_N [0, 0x70]))],
   Jumpi),
  (75, [(75, Dup 0), (76, Stack (PUSH_N [0x8F, 0x95, 0x95, 0xD4])), (81, Arith inst_EQ),
        (82, Stack (PUSH_N [0, 0x83]))],
   Jumpi),
  (86, [(86, Pc JUMPDEST), (87, Stack (PUSH_N [0])), (89, Dup 0), (90, Unknown 0xFD)], Terminal),
  (91, [(91, Pc JUMPDEST), (92, Info CALLVALUE), (93, Arith ISZERO), (94, Stack (PUSH_N [0, 0x66]))], Jumpi),
  (98, [(98, Stack (PUSH_N [0])), (100, Dup 0), (101, Unknown 0xFD)], Terminal),
  (102, [(102, Pc JUMPDEST), (103, Stack (PUSH_N [0, 0x6E])), (106, Stack (PUSH_N [0, 0x8B]))], Jump),
  (110, [(110, Pc JUMPDEST), (111, Misc STOP)], Terminal),
  (112, [(112, Pc JUMPDEST), (113, Info CALLVALUE), (114, Arith ISZERO), (115, Stack (PUSH_N [0, 0x7B]))],
   Jumpi),
  (119, [(119, Stack (PUSH_N [0])), (121, Dup 0), (122, Unknown 0xFD)], Terminal),
  (123, [(123, Pc JUMPDEST), (124, Stack (PUSH_N [0, 0x6E])), (127, Stack (PUSH_N [0, 0xCE]))], Jump),
  (131, [(131, Pc JUMPDEST), (132, Stack (PUSH_N [0, 0x6E])), (135, Stack (PUSH_N [1, 0x11]))], Jump),
  (139, [(139, Pc JUMPDEST), (140, Stack (PUSH_N [2])), (142, Storage SLOAD), (143, Info CALLER),
         (144, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (165, Swap 0), (166, Dup 1), (167, Bits inst_AND), (168, Swap 1), (169, Bits inst_AND),
         (170, Arith inst_EQ), (171, Stack (PUSH_N [0, 0xB3]))],
   Jumpi),
  (175, [(175, Stack (PUSH_N [0])), (177, Dup 0), (178, Unknown 0xFD)], Terminal),
  (179, [(179, Pc JUMPDEST), (180, Stack (PUSH_N [1])), (182, Storage SLOAD),
         (183, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (204, Bits inst_AND), (205, Misc SUICIDE)],
   Terminal),
  (206, [(206, Pc JUMPDEST), (207, Stack (PUSH_N [2])), (209, Storage SLOAD), (210, Info CALLER),
         (211, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (232, Swap 0), (233, Dup 1), (234, Bits inst_AND), (235, Swap 1), (236, Bits inst_AND),
         (237, Arith inst_EQ), (238, Stack (PUSH_N [0, 0xF6]))],
   Jumpi),
  (242, [(242, Stack (PUSH_N [0])), (244, Dup 0), (245, Unknown 0xFD)], Terminal),
  (246, [(246, Pc JUMPDEST), (247, Stack (PUSH_N [0])), (249, Storage SLOAD),
         (250, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (271, Bits inst_AND), (272, Misc SUICIDE)],
   Terminal),
  (273, [(273, Pc JUMPDEST), (274, Stack (PUSH_N [0])), (276, Storage SLOAD), (277, Info CALLER),
         (278, Stack (PUSH_N
                       [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
         (299, Swap 0), (300, Dup 1), (301, Bits inst_AND), (302, Swap 1), (303, Bits inst_AND),
         (304, Arith inst_EQ), (305, Stack (PUSH_N [1, 0x39]))],
   Jumpi),
  (309, [(309, Stack (PUSH_N [0])), (311, Dup 0), (312, Unknown 0xFD)], Terminal),
  (313, [(313, Pc JUMPDEST)], Jump), (315, [(315, Misc STOP)], Terminal),
  (316, [(316, Log LOG1), (317, Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58])), (324, Arith SHA3),
         (325, Stack (PUSH_N
                       [0xD2, 0xEE, 0x80, 0x51, 0xB0, 0x98, 0xC7, 0x99, 0xDF, 0x41, 0x46, 0x65, 0x99, 0xCD,
                        0x31, 0x1E, 0x37, 0x6F, 0xD3, 0x63, 0x72, 0xF2, 0xBE, 0xCE, 0xC0, 0x8F, 0xE4, 0x94])),
         (354, Unknown 0xBA)],
   Terminal),
  (355, [(355, Memory EXTCODECOPY), (356, Unknown 0xC1)], Terminal), (357, [(357, Misc STOP)], Terminal),
  (358, [(358, Unknown 0x29)], Terminal)]"
  by eval

definition addfund_hash :: "32 word"  where
 "addfund_hash = 0x8f9595d4"

definition pay_hash :: "32 word"  where
 "pay_hash = 0x1b9265b8"

definition refund_hash :: "32 word"  where
 "refund_hash = 0x590e1ae3"

definition return_action ::"address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> 32 word \<Rightarrow> w256 \<Rightarrow> contract_action" where
  "return_action sender from to owner hash v = 
 (if hash = addfund_hash \<and> sender = from  \<and> v \<noteq> 0then
    ContractReturn []
  else if hash = refund_hash \<and> sender = owner \<and> v = 0 then
    ContractSuicide from
  else if hash = pay_hash \<and> sender = owner \<and> v = 0 then
    ContractSuicide to
  else
    ContractFail [ShouldNotHappen])"

context
notes
  words_simps[simp add]
  calldataload_simps[simp add]
  M_def[simp add]
  Cmem_def[simp add]
  memory_range.simps[simp del]
 if_split[ split del ] sep_fun_simps[simp del]
gas_value_simps[simp add] pure_emp_simps[simp add]
evm_fun_simps[simp add] sep_lc[simp del] sep_conj_first[simp add]
pure_false_simps[simp add] iszero_stack_def[simp add]
word256FromNat_def[simp add]
begin
abbreviation "blk_num \<equiv> block_number_pred"

lemma address_mask:
 "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = mask 160"
  by (simp add: mask_def)

lemma address_mask_ucast:
 "ucast (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF && (ucast (w::address))::w256) = w"
  apply (simp add: ucast_ucast_mask address_mask ucast_mask_drop word_bool_alg.conj.commute)
  apply (simp add: mask_def)
  done

lemma ucast_and_w256_drop:
 "((ucast (w::address))::w256) && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = ucast w"
  by word_bitwise

definition
  bytestr_to_w256 :: "byte list \<Rightarrow> w256"  where
 "bytestr_to_w256 \<equiv> word_rcat"

lemma hash_diff:
  "ucast (hash::32 word) = (0x1B9265B8::w256) \<Longrightarrow> hash = 0x1B9265B8 "
  "ucast (hash::32 word) = (0x590E1AE3::w256) \<Longrightarrow> hash = 0x590E1AE3 "
  "ucast (hash::32 word) = (0x8f9595d4::w256) \<Longrightarrow> hash = 0x8f9595d4 "
  by word_bitwise+

method sep_imp_solve2 =
(clarsimp?),
(rule conjI),
  (clarsimp simp add: )?,
  order_sep_conj?,
  (sep_cancel, simp?)+,
  (erule instantiate_emp)?,
(fastforce simp add:word_rcat_simps)?

theorem verify_escrow_return:
notes
  bit_mask_rev[simp add]
  address_mask_ucast[simp] address_mask_ucast[simplified word_bool_alg.conj.commute, simp]
  ucast_and_w256_drop[simp]
  addfund_hash_def[simp] refund_hash_def[simp] pay_hash_def[simp]
  word_bool_alg.conj.commute[simp]
  length_word_rsplit_4[simp]
assumes blk_num[simp]: "bn > 2463000"
and net[simp]: "at_least_eip150 net"
and from_neq_to: "from \<noteq> to"
and from_neq_owner: "from \<noteq> owner"
shows
"\<exists>r. triple 
  (program_counter 0 ** stack_height 0 ** (sent_data (word_rsplit (hash::32 word)::byte list))
   ** sent_value v ** caller sender ** blk_num bn **
   memory_usage 0 ** continuing ** gas_pred 100000
   ** storage 0 (ucast from)
   ** storage 1 (ucast to)
   ** storage 2 (ucast owner)
   ** account_existence a b 
   ** memory (word_rcat [64::byte]) (bytestr_to_w256 [x]) **
   memory (word_rcat [96::byte]) (bytestr_to_w256 [y]))
  blocks_escrow (action (return_action sender from to owner hash v) ** r)"
  apply (insert blk_num[simplified word_less_nat_alt] net)
  apply (simp add:blocks_escrow_simp)
  apply(simp add: return_action_def blocks_simps triple_def )
  apply(split if_split, rule conjI)
   apply(rule impI, ((erule conjE)+)?, rule exI)
   apply((block_vcg)+)[1]
  apply (rule net)
   apply (rule conjI, (sep_cancel, clarsimp?)+, simp)+
   apply((block_vcg)+)[1]
   apply sep_cancel
   apply (simp)
   apply clarsimp
   apply(split if_split, rule conjI )
   apply(rule impI, ((erule conjE)+)?, rule exI)
   apply((block_vcg)+)[1]
  apply (rule net)
   apply (rule conjI, (sep_cancel, clarsimp?)+, simp)+
    apply (simp)+
  apply((block_vcg)+)[1]
  apply (rule net)
  apply (rule conjI, (sep_cancel, clarsimp?)+, simp)+
  apply (rule conjI, (sep_cancel, clarsimp?)+)
  apply (rule net)
  apply (sep_cancel)
   apply simp
  apply(split if_split, rule conjI )
  apply((rule impI)+, ((erule conjE)+)?, rule exI)
  apply((block_vcg)+)[1]
  apply (rule net)
  apply (rule conjI, (sep_cancel, clarsimp?)+, simp)+
  apply((block_vcg)+)[1]
  apply (rule net)
  apply (rule conjI, (sep_cancel, clarsimp?)+, simp)+
  apply (rule conjI, (sep_cancel)+)+
  apply simp
  apply (rule net)
  apply (clarsimp simp:  split:if_split_asm)+
    apply sep_cancel+
   apply simp
  using from_neq_to from_neq_owner
  apply (clarsimp)
  apply (case_tac "v = 0" ; clarsimp)
  apply (case_tac "sender = owner"; clarsimp)
  apply (case_tac "hash \<in> {pay_hash, refund_hash, addfund_hash}")
  apply (case_tac "from \<noteq> sender"; clarsimp)
  apply(rule exI)
  apply((block_vcg| rule net)+)[1]
  apply (rule conjI, (sep_cancel, clarsimp?)+, simp)+
  apply (simp add: hash_diff eval_bit_mask)+
  apply (clarsimp split:if_splits simp:word_rcat_simps bin_cat_def hash_diff)
    apply(((blocks_rule_vcg; (rule refl)?), triple_seq_vcg))
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])
  apply (drule ucast_up_inj; simp)
  apply (clarsimp split:if_splits simp:word_rcat_simps bin_cat_def hash_diff)
  apply(((blocks_rule_vcg; (rule refl)?), triple_seq_vcg))
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (rule exI)
  apply((block_vcg| rule net)+)[1]
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (split if_split ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply((block_vcg| rule net)+)[1]
  apply (clarsimp simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (clarsimp split:if_splits simp:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply((block_vcg| rule net)+)[1]
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (case_tac "hash \<in> {refund_hash,pay_hash,addfund_hash}"; simp)
  apply ( erule disjE)+
  apply (rule exI)
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)+
  apply (drule ucast_up_inj; simp)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)+
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (rule exI)
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)+
  apply (drule ucast_up_inj; simp)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)+
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)+
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (erule disjE; (drule ucast_up_inj; simp) )
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (erule disjE)
  apply (clarsimp dest:  ucast_up_inj )
  apply (clarsimp dest:  ucast_up_inj )
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (erule disjE)
  apply (clarsimp dest:  ucast_up_inj )
  apply (clarsimp dest:  ucast_up_inj )
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (drule  ucast_up_inj; simp )
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply((block_vcg| rule net)+)[1]
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  apply (split if_split_asm ; simp add:hash_diff eval_bit_mask)+
  apply((block_vcg| rule net)+)[1]
  apply(clarsimp?, ((((sep_cancel, clarsimp?)+)|simp add:word_rcat_simps|rule conjI)+)[1])+
  
  apply((block_vcg| rule net)+)[1]
  oops

  oops

lemma
  "ucast (hash::32 word) = (v::w256) \<Longrightarrow> v < 2^32 \<Longrightarrow>
         hash = (ucast v) "

  apply (simp add: ucast_def)
  
  apply (rule sym)
  apply (rule word_uint.Rep_inverse')
  apply (simp add: word_uint.Rep_inverse)
  apply unat_arith
  oops
  oops
end