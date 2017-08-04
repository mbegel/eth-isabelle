theory Dispatcher

imports
  "../Parse"
  "../Hoare/HoareBasicBlocks"
  "./ToyExamplesBlocks"

begin

definition 
dispatch1_hash :: "32 word"
where
"dispatch1_hash == 0x3ecb5edf"

definition 
dispatch2_hash :: "32 word"
where
"dispatch2_hash == 0x8cd5b077"

lemmas blocks_simps = build_blocks_def byteListInt_def find_block_def extract_indexes_def build_vertices_def
 aux_basic_block.simps add_address_def block_pt_def

value "parse_bytecode ''90''"

value"blocks_list (build_blocks (parse_bytecode ''60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680633ecb5edf1460475780638cd5b07714607b575b600080fd5b3415605157600080fd5b6065600480803590602001909190505060a1565b6040518082815260200191505060405180910390f35b3415608557600080fd5b608b60ad565b6040518082815260200191505060405180910390f35b6000600190505b919050565b6000600290505b905600a165627a7a72305820c9cf1e9d83721f6f9afecea62b7e868d98502ee8556dcaf6abb24acb8bc0d9fb0029''))"

definition insts where
"insts \<equiv>
[Stack (PUSH_N [96]), Stack (PUSH_N [64]), Memory MSTORE, Stack (PUSH_N [0]), Stack CALLDATALOAD,
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Swap 0, Arith DIV, Stack (PUSH_N [255, 255, 255, 255]), Bits inst_AND, Dup 0,
  Stack (PUSH_N [62, 203, 94, 223]), Arith inst_EQ, Stack (PUSH_N [71]), Pc JUMPI, Dup 0,
  Stack (PUSH_N [140, 213, 176, 119]), Arith inst_EQ, Stack (PUSH_N [123]), Pc JUMPI, Pc JUMPDEST,
  Stack (PUSH_N [0]), Dup 0, Unknown 253, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [81]),
  Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 253, Pc JUMPDEST, Stack (PUSH_N [101]), Stack (PUSH_N [4]),
  Dup 0, Dup 0, Stack CALLDATALOAD, Swap 0, Stack (PUSH_N [32]), Arith ADD, Swap 0, Swap 1, Swap 0, Stack POP,
  Stack POP, Stack (PUSH_N [161]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [64]), Memory MLOAD, Dup 0, Dup 2,
  Dup 1, Memory MSTORE, Stack (PUSH_N [32]), Arith ADD, Swap 1, Stack POP, Stack POP, Stack (PUSH_N [64]),
  Memory MLOAD, Dup 0, Swap 1, Arith SUB, Swap 0, Misc RETURN, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO,
  Stack (PUSH_N [133]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 253, Pc JUMPDEST, Stack (PUSH_N [139]),
  Stack (PUSH_N [173]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [64]), Memory MLOAD, Dup 0, Dup 2, Dup 1,
  Memory MSTORE, Stack (PUSH_N [32]), Arith ADD, Swap 1, Stack POP, Stack POP, Stack (PUSH_N [64]),
  Memory MLOAD, Dup 0, Swap 1, Arith SUB, Swap 0, Misc RETURN, Pc JUMPDEST, Stack (PUSH_N [0]),
  Stack (PUSH_N [1]), Swap 0, Stack POP, Pc JUMPDEST, Swap 1, Swap 0, Stack POP, Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [0]), Stack (PUSH_N [2]), Swap 0, Stack POP, Pc JUMPDEST, Swap 0, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [98, 122, 122, 114, 48, 88]), Arith SHA3, Unknown 201, Unknown 207, Unknown 30, Swap 13, Dup 3,
  Stack (PUSH_N [31, 111, 154, 254, 206, 166, 43, 126, 134, 141, 152, 80, 46, 232, 85, 109, 202, 246, 171]),
  Unknown 178, Unknown 74, Unknown 203, Dup 02, Unknown 192, Unknown 217, Unknown 251, Misc STOP, Unknown 41]"

definition blocks where
"blocks =
\<lparr>blocks_indexes = [0, 56, 66, 71, 77, 81, 101, 123, 129, 133, 139, 161, 168, 173, 180, 183, 184, 226],
    blocks_list = map_of [(0, [(0, Stack (PUSH_N [96])), (2, Stack (PUSH_N [64])), (4, Memory MSTORE), (5, Stack (PUSH_N [0])),
            (7, Stack CALLDATALOAD),
            (8, Stack (PUSH_N
                        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                         0])),
            (38, Swap 0), (39, Arith DIV), (40, Stack (PUSH_N [255, 255, 255, 255])), (45, Bits inst_AND),
            (46, Dup 0), (47, Stack (PUSH_N [62, 203, 94, 223])), (52, Arith inst_EQ),
            (53, Stack (PUSH_N [71]))],
        Jumpi),
       (56, [(56, Dup 0), (57, Stack (PUSH_N [140, 213, 176, 119])), (62, Arith inst_EQ),
             (63, Stack (PUSH_N [123]))],
        Jumpi),
       (66, [(66, Pc JUMPDEST), (67, Stack (PUSH_N [0])), (69, Dup 0), (70, Unknown 253)], Next),
       (71, [(71, Pc JUMPDEST), (72, Info CALLVALUE), (73, Arith ISZERO), (74, Stack (PUSH_N [81]))], Jumpi),
       (77, [(77, Stack (PUSH_N [0])), (79, Dup 0), (80, Unknown 253)], Next),
       (81, [(81, Pc JUMPDEST), (82, Stack (PUSH_N [101])), (84, Stack (PUSH_N [4])), (86, Dup 0), (87, Dup 0),
             (88, Stack CALLDATALOAD), (89, Swap 0), (90, Stack (PUSH_N [32])), (92, Arith ADD), (93, Swap 0),
             (94, Swap 1), (95, Swap 0), (96, Stack POP), (97, Stack POP), (98, Stack (PUSH_N [161]))],
        Jump),
       (101, [(101, Pc JUMPDEST), (102, Stack (PUSH_N [64])), (104, Memory MLOAD), (105, Dup 0), (106, Dup 2),
              (107, Dup 1), (108, Memory MSTORE), (109, Stack (PUSH_N [32])), (111, Arith ADD), (112, Swap 1),
              (113, Stack POP), (114, Stack POP), (115, Stack (PUSH_N [64])), (117, Memory MLOAD),
              (118, Dup 0), (119, Swap 1), (120, Arith SUB), (121, Swap 0), (122, Misc RETURN)],
        No),
       (123, [(123, Pc JUMPDEST), (124, Info CALLVALUE), (125, Arith ISZERO), (126, Stack (PUSH_N [133]))],
        Jumpi),
       (129, [(129, Stack (PUSH_N [0])), (131, Dup 0), (132, Unknown 253)], Next),
       (133, [(133, Pc JUMPDEST), (134, Stack (PUSH_N [139])), (136, Stack (PUSH_N [173]))], Jump),
       (139, [(139, Pc JUMPDEST), (140, Stack (PUSH_N [64])), (142, Memory MLOAD), (143, Dup 0), (144, Dup 2),
              (145, Dup 1), (146, Memory MSTORE), (147, Stack (PUSH_N [32])), (149, Arith ADD), (150, Swap 1),
              (151, Stack POP), (152, Stack POP), (153, Stack (PUSH_N [64])), (155, Memory MLOAD),
              (156, Dup 0), (157, Swap 1), (158, Arith SUB), (159, Swap 0), (160, Misc RETURN)],
        No),
       (161, [(161, Pc JUMPDEST), (162, Stack (PUSH_N [0])), (164, Stack (PUSH_N [1])), (166, Swap 0),
              (167, Stack POP)],
        Next),
       (168, [(168, Pc JUMPDEST), (169, Swap 1), (170, Swap 0), (171, Stack POP)], Jump),
       (173, [(173, Pc JUMPDEST), (174, Stack (PUSH_N [0])), (176, Stack (PUSH_N [2])), (178, Swap 0),
              (179, Stack POP)],
        Next),
       (180, [(180, Pc JUMPDEST), (181, Swap 0)], Jump), (183, [(183, Misc STOP)], No),
       (184, [(184, Log LOG1), (185, Stack (PUSH_N [98, 122, 122, 114, 48, 88])), (192, Arith SHA3),
              (193, Unknown 201), (194, Unknown 207), (195, Unknown 30), (196, Swap 13), (197, Dup 3),
              (198, Stack (PUSH_N
                            [31, 111, 154, 254, 206, 166, 43, 126, 134, 141, 152, 80, 46, 232, 85, 109, 202,
                             246, 171])),
              (218, Unknown 178), (219, Unknown 74), (220, Unknown 203), (221, Dup 02), (222, Unknown 192),
              (223, Unknown 217), (224, Unknown 251), (225, Misc STOP)],
        No),
       (226, [(226, Unknown 41)], Next)],
    all_blocks =
      [(0, [(0, Stack (PUSH_N [96])), (2, Stack (PUSH_N [64])), (4, Memory MSTORE), (5, Stack (PUSH_N [0])),
            (7, Stack CALLDATALOAD),
            (8, Stack (PUSH_N
                        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                         0])),
            (38, Swap 0), (39, Arith DIV), (40, Stack (PUSH_N [255, 255, 255, 255])), (45, Bits inst_AND),
            (46, Dup 0), (47, Stack (PUSH_N [62, 203, 94, 223])), (52, Arith inst_EQ),
            (53, Stack (PUSH_N [71]))],
        Jumpi),
       (56, [(56, Dup 0), (57, Stack (PUSH_N [140, 213, 176, 119])), (62, Arith inst_EQ),
             (63, Stack (PUSH_N [123]))],
        Jumpi),
       (66, [(66, Pc JUMPDEST), (67, Stack (PUSH_N [0])), (69, Dup 0), (70, Unknown 253)], Next),
       (71, [(71, Pc JUMPDEST), (72, Info CALLVALUE), (73, Arith ISZERO), (74, Stack (PUSH_N [81]))], Jumpi),
       (77, [(77, Stack (PUSH_N [0])), (79, Dup 0), (80, Unknown 253)], Next),
       (81, [(81, Pc JUMPDEST), (82, Stack (PUSH_N [101])), (84, Stack (PUSH_N [4])), (86, Dup 0), (87, Dup 0),
             (88, Stack CALLDATALOAD), (89, Swap 0), (90, Stack (PUSH_N [32])), (92, Arith ADD), (93, Swap 0),
             (94, Swap 1), (95, Swap 0), (96, Stack POP), (97, Stack POP), (98, Stack (PUSH_N [161]))],
        Jump),
       (101, [(101, Pc JUMPDEST), (102, Stack (PUSH_N [64])), (104, Memory MLOAD), (105, Dup 0), (106, Dup 2),
              (107, Dup 1), (108, Memory MSTORE), (109, Stack (PUSH_N [32])), (111, Arith ADD), (112, Swap 1),
              (113, Stack POP), (114, Stack POP), (115, Stack (PUSH_N [64])), (117, Memory MLOAD),
              (118, Dup 0), (119, Swap 1), (120, Arith SUB), (121, Swap 0), (122, Misc RETURN)],
        No),
       (123, [(123, Pc JUMPDEST), (124, Info CALLVALUE), (125, Arith ISZERO), (126, Stack (PUSH_N [133]))],
        Jumpi),
       (129, [(129, Stack (PUSH_N [0])), (131, Dup 0), (132, Unknown 253)], Next),
       (133, [(133, Pc JUMPDEST), (134, Stack (PUSH_N [139])), (136, Stack (PUSH_N [173]))], Jump),
       (139, [(139, Pc JUMPDEST), (140, Stack (PUSH_N [64])), (142, Memory MLOAD), (143, Dup 0), (144, Dup 2),
              (145, Dup 1), (146, Memory MSTORE), (147, Stack (PUSH_N [32])), (149, Arith ADD), (150, Swap 1),
              (151, Stack POP), (152, Stack POP), (153, Stack (PUSH_N [64])), (155, Memory MLOAD),
              (156, Dup 0), (157, Swap 1), (158, Arith SUB), (159, Swap 0), (160, Misc RETURN)],
        No),
       (161, [(161, Pc JUMPDEST), (162, Stack (PUSH_N [0])), (164, Stack (PUSH_N [1])), (166, Swap 0),
              (167, Stack POP)],
        Next),
       (168, [(168, Pc JUMPDEST), (169, Swap 1), (170, Swap 0), (171, Stack POP)], Jump),
       (173, [(173, Pc JUMPDEST), (174, Stack (PUSH_N [0])), (176, Stack (PUSH_N [2])), (178, Swap 0),
              (179, Stack POP)],
        Next),
       (180, [(180, Pc JUMPDEST), (181, Swap 0)], Jump), (183, [(183, Misc STOP)], No),
       (184, [(184, Log LOG1), (185, Stack (PUSH_N [98, 122, 122, 114, 48, 88])), (192, Arith SHA3),
              (193, Unknown 201), (194, Unknown 207), (195, Unknown 30), (196, Swap 13), (197, Dup 3),
              (198, Stack (PUSH_N
                            [31, 111, 154, 254, 206, 166, 43, 126, 134, 141, 152, 80, 46, 232, 85, 109, 202,
                             246, 171])),
              (218, Unknown 178), (219, Unknown 74), (220, Unknown 203), (221, Dup 02), (222, Unknown 192),
              (223, Unknown 217), (224, Unknown 251), (225, Misc STOP)],
        No),
       (226, [(226, Unknown 41)], Next)]\<rparr>"
context
notes if_split[ split del ] sep_fun_simps[simp del]
gas_value_simps[simp add] pure_emp_simps[simp add]
evm_fun_simps[simp add] sep_lc[simp del] sep_conj_first[simp add]
pure_false_simps[simp add] iszero_stack_def[simp add]
begin

lemma aux1:
"(word_of_int (bin_rcat 8 [62, 203, 94, 223]) ::w256)=
    word_of_int (bin_rcat 8 [255, 255, 255, 255]) AND
    (if word_of_int
         (bin_rcat 8
           [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) =
        (0::w256)
     then word_of_int 0
     else word_of_int
           (uint
             (read_word_from_bytes
               (unat (word_of_int (bin_rcat 8 [0])))
               (word_rsplit dispatch1_hash)) div
            uint
             (word_of_int
               (bin_rcat 8
                 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])::w256)))"
apply(split if_splits)
 apply(simp add: bin_rcat_def bin_cat_def)
unfolding read_word_from_bytes_def dispatch1_hash_def
apply simp
apply (simp add: byte_list_fill_right_def)
apply (simp add: word_rcat_def bin_rcat_def bin_cat_def  )
done

method sep_imp_solve =
clarsimp?;
(rule conjI),
  (clarsimp simp add: word_rcat_def)?,
  (sep_cancel)+,
  (erule instantiate_emp)?,
(simp add:M_def Cmem_def bin_rcat_def)?

method sep_imp_solve_sep_cancel_simp =
(clarsimp),
(rule conjI),
  (clarsimp simp add: word_rcat_def)?,
  (sep_cancel, simp?)+,
  (erule instantiate_emp)?,
(simp add:M_def Cmem_def bin_rcat_def)?
value "word_rsplit (0x3ecb5edf::32 word):: byte list"
lemma
"\<exists>r.
triple 
  (
program_counter 0 ** stack_height 0 ** (data_lst 0 (word_rsplit dispatch1_hash)) ** sent_value 0 **
   memory_usage 0 ** continuing ** gas_pred 3000 ** memory (word_rcat [64::byte]) (word_rcat [x::byte]::256 word))
  blocks
  (action (ContractReturn (word_rsplit (1:: w256))) ** r)"
apply (simp add: blocks_def triple_def)
apply(rule exI)
apply(triple_jumpi_vcg)
    apply(simp add: Cmem_def M_def word_rsplit_def bin_rsplit_def)
   apply(sep_imp_solve_sep_cancel_simp | sep_imp_solve)+
  apply(simp add: bin_rcat_def)
 apply(simp add: aux1)
 defer
 apply(simp add: aux1)
 apply(subst sym[OF aux1])
 apply(simp add: bin_rcat_def)
apply((rule blocks_jumpi; (rule refl)?), triple_seq_vcg)
apply(sep_imp_solve_sep_cancel_simp | sep_imp_solve)+
apply(simp add: bin_rcat_def)+
defer 
apply(simp)
apply((rule blocks_jump; (rule refl)?), triple_seq_vcg)
apply(sep_imp_solve_sep_cancel_simp | sep_imp_solve)+
apply(simp add: bin_rcat_def)+
apply((rule blocks_next; (rule refl)?), triple_seq_vcg)
apply(sep_imp_solve_sep_cancel_simp | sep_imp_solve)+
apply(simp add: bin_rcat_def)+
apply((rule blocks_jump; (rule refl)?), triple_seq_vcg)
apply(sep_imp_solve_sep_cancel_simp | sep_imp_solve)
apply(sep_imp_solve_sep_cancel_simp | sep_imp_solve)
apply(sep_imp_solve_sep_cancel_simp | sep_imp_solve)
apply(sep_imp_solve_sep_cancel_simp | sep_imp_solve)
apply(clarsimp)
apply(rule conjI)
apply  (clarsimp simp add: word_rcat_def)?
apply  (sep_cancel, simp?)+
apply  (erule instantiate_emp)?
(simp add:M_def Cmem_def bin_rcat_def)?
apply(sep_imp_solve_sep_cancel_simp | sep_imp_solve)
apply(simp add: bin_rcat_def)+
sorry
value "word_rsplit (0x3ecb5edf::w256):: byte list"
value "byte_list_fill_right  0 32 ([62, 203, 94, 223]::byte list)"
end
end