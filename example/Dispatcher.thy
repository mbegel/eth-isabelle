theory Dispatcher

imports
  "../Parse"
  "../attic/BasicBlocks"
  "../Hoare/Hoare"

begin

definition 
dispatch1_hash :: "256 word"
where
"dispatch1_hash == 0x3ecb5edf"

definition 
dispatch2_hash :: "256 word"
where
"dispatch2_hash == 0x8cd5b077"

lemmas blocks_simps = build_blocks_def byteListInt_def find_block_def extract_indexes_def build_vertices_def
 aux_basic_block.simps add_address_def block_pt_def



value"blocks_list (build_blocks (parse_bytecode ''60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff1680633ecb5edf1460475780638cd5b07714607b575b600080fd5b3415605157600080fd5b6065600480803590602001909190505060a1565b6040518082815260200191505060405180910390f35b3415608557600080fd5b608b60ad565b6040518082815260200191505060405180910390f35b6000600190505b919050565b6000600290505b905600a165627a7a72305820c9cf1e9d83721f6f9afecea62b7e868d98502ee8556dcaf6abb24acb8bc0d9fb0029''))"

definition insts where
"insts \<equiv>
[Stack (PUSH_N [96]), Stack (PUSH_N [64]), Memory MSTORE, Stack (PUSH_N [0]), Stack CALLDATALOAD,
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Swap 1, Arith DIV, Stack (PUSH_N [255, 255, 255, 255]), Bits inst_AND, Dup 1,
  Stack (PUSH_N [62, 203, 94, 223]), Arith inst_EQ, Stack (PUSH_N [71]), Pc JUMPI, Dup 1,
  Stack (PUSH_N [140, 213, 176, 119]), Arith inst_EQ, Stack (PUSH_N [123]), Pc JUMPI, Pc JUMPDEST,
  Stack (PUSH_N [0]), Dup 1, Unknown 253, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [81]),
  Pc JUMPI, Stack (PUSH_N [0]), Dup 1, Unknown 253, Pc JUMPDEST, Stack (PUSH_N [101]), Stack (PUSH_N [4]),
  Dup 1, Dup 1, Stack CALLDATALOAD, Swap 1, Stack (PUSH_N [32]), Arith ADD, Swap 1, Swap 2, Swap 1, Stack POP,
  Stack POP, Stack (PUSH_N [161]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [64]), Memory MLOAD, Dup 1, Dup 3,
  Dup 2, Memory MSTORE, Stack (PUSH_N [32]), Arith ADD, Swap 2, Stack POP, Stack POP, Stack (PUSH_N [64]),
  Memory MLOAD, Dup 1, Swap 2, Arith SUB, Swap 1, Misc RETURN, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO,
  Stack (PUSH_N [133]), Pc JUMPI, Stack (PUSH_N [0]), Dup 1, Unknown 253, Pc JUMPDEST, Stack (PUSH_N [139]),
  Stack (PUSH_N [173]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [64]), Memory MLOAD, Dup 1, Dup 3, Dup 2,
  Memory MSTORE, Stack (PUSH_N [32]), Arith ADD, Swap 2, Stack POP, Stack POP, Stack (PUSH_N [64]),
  Memory MLOAD, Dup 1, Swap 2, Arith SUB, Swap 1, Misc RETURN, Pc JUMPDEST, Stack (PUSH_N [0]),
  Stack (PUSH_N [1]), Swap 1, Stack POP, Pc JUMPDEST, Swap 2, Swap 1, Stack POP, Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [0]), Stack (PUSH_N [2]), Swap 1, Stack POP, Pc JUMPDEST, Swap 1, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [98, 122, 122, 114, 48, 88]), Arith SHA3, Unknown 201, Unknown 207, Unknown 30, Swap 14, Dup 4,
  Stack (PUSH_N [31, 111, 154, 254, 206, 166, 43, 126, 134, 141, 152, 80, 46, 232, 85, 109, 202, 246, 171]),
  Unknown 178, Unknown 74, Unknown 203, Dup 12, Unknown 192, Unknown 217, Unknown 251, Misc STOP, Unknown 41]"

definition blocks where
"blocks =
\<lparr>blocks_indexes = [0, 56, 66, 71, 77, 81, 101, 123, 129, 133, 139, 161, 168, 173, 180, 183, 184, 226],
    blocks_list = map_of [(0, [(0, Stack (PUSH_N [96])), (2, Stack (PUSH_N [64])), (4, Memory MSTORE), (5, Stack (PUSH_N [0])),
            (7, Stack CALLDATALOAD),
            (8, Stack (PUSH_N
                        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                         0])),
            (38, Swap 1), (39, Arith DIV), (40, Stack (PUSH_N [255, 255, 255, 255])), (45, Bits inst_AND),
            (46, Dup 1), (47, Stack (PUSH_N [62, 203, 94, 223])), (52, Arith inst_EQ),
            (53, Stack (PUSH_N [71]))],
        Jumpi),
       (56, [(56, Dup 1), (57, Stack (PUSH_N [140, 213, 176, 119])), (62, Arith inst_EQ),
             (63, Stack (PUSH_N [123]))],
        Jumpi),
       (66, [(66, Pc JUMPDEST), (67, Stack (PUSH_N [0])), (69, Dup 1), (70, Unknown 253)], Next),
       (71, [(71, Pc JUMPDEST), (72, Info CALLVALUE), (73, Arith ISZERO), (74, Stack (PUSH_N [81]))], Jumpi),
       (77, [(77, Stack (PUSH_N [0])), (79, Dup 1), (80, Unknown 253)], Next),
       (81, [(81, Pc JUMPDEST), (82, Stack (PUSH_N [101])), (84, Stack (PUSH_N [4])), (86, Dup 1), (87, Dup 1),
             (88, Stack CALLDATALOAD), (89, Swap 1), (90, Stack (PUSH_N [32])), (92, Arith ADD), (93, Swap 1),
             (94, Swap 2), (95, Swap 1), (96, Stack POP), (97, Stack POP), (98, Stack (PUSH_N [161]))],
        Jump),
       (101, [(101, Pc JUMPDEST), (102, Stack (PUSH_N [64])), (104, Memory MLOAD), (105, Dup 1), (106, Dup 3),
              (107, Dup 2), (108, Memory MSTORE), (109, Stack (PUSH_N [32])), (111, Arith ADD), (112, Swap 2),
              (113, Stack POP), (114, Stack POP), (115, Stack (PUSH_N [64])), (117, Memory MLOAD),
              (118, Dup 1), (119, Swap 2), (120, Arith SUB), (121, Swap 1), (122, Misc RETURN)],
        No),
       (123, [(123, Pc JUMPDEST), (124, Info CALLVALUE), (125, Arith ISZERO), (126, Stack (PUSH_N [133]))],
        Jumpi),
       (129, [(129, Stack (PUSH_N [0])), (131, Dup 1), (132, Unknown 253)], Next),
       (133, [(133, Pc JUMPDEST), (134, Stack (PUSH_N [139])), (136, Stack (PUSH_N [173]))], Jump),
       (139, [(139, Pc JUMPDEST), (140, Stack (PUSH_N [64])), (142, Memory MLOAD), (143, Dup 1), (144, Dup 3),
              (145, Dup 2), (146, Memory MSTORE), (147, Stack (PUSH_N [32])), (149, Arith ADD), (150, Swap 2),
              (151, Stack POP), (152, Stack POP), (153, Stack (PUSH_N [64])), (155, Memory MLOAD),
              (156, Dup 1), (157, Swap 2), (158, Arith SUB), (159, Swap 1), (160, Misc RETURN)],
        No),
       (161, [(161, Pc JUMPDEST), (162, Stack (PUSH_N [0])), (164, Stack (PUSH_N [1])), (166, Swap 1),
              (167, Stack POP)],
        Next),
       (168, [(168, Pc JUMPDEST), (169, Swap 2), (170, Swap 1), (171, Stack POP)], Jump),
       (173, [(173, Pc JUMPDEST), (174, Stack (PUSH_N [0])), (176, Stack (PUSH_N [2])), (178, Swap 1),
              (179, Stack POP)],
        Next),
       (180, [(180, Pc JUMPDEST), (181, Swap 1)], Jump), (183, [(183, Misc STOP)], No),
       (184, [(184, Log LOG1), (185, Stack (PUSH_N [98, 122, 122, 114, 48, 88])), (192, Arith SHA3),
              (193, Unknown 201), (194, Unknown 207), (195, Unknown 30), (196, Swap 14), (197, Dup 4),
              (198, Stack (PUSH_N
                            [31, 111, 154, 254, 206, 166, 43, 126, 134, 141, 152, 80, 46, 232, 85, 109, 202,
                             246, 171])),
              (218, Unknown 178), (219, Unknown 74), (220, Unknown 203), (221, Dup 12), (222, Unknown 192),
              (223, Unknown 217), (224, Unknown 251), (225, Misc STOP)],
        No),
       (226, [(226, Unknown 41)], Next)],
    all_blocks =
      [(0, [(0, Stack (PUSH_N [96])), (2, Stack (PUSH_N [64])), (4, Memory MSTORE), (5, Stack (PUSH_N [0])),
            (7, Stack CALLDATALOAD),
            (8, Stack (PUSH_N
                        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                         0])),
            (38, Swap 1), (39, Arith DIV), (40, Stack (PUSH_N [255, 255, 255, 255])), (45, Bits inst_AND),
            (46, Dup 1), (47, Stack (PUSH_N [62, 203, 94, 223])), (52, Arith inst_EQ),
            (53, Stack (PUSH_N [71]))],
        Jumpi),
       (56, [(56, Dup 1), (57, Stack (PUSH_N [140, 213, 176, 119])), (62, Arith inst_EQ),
             (63, Stack (PUSH_N [123]))],
        Jumpi),
       (66, [(66, Pc JUMPDEST), (67, Stack (PUSH_N [0])), (69, Dup 1), (70, Unknown 253)], Next),
       (71, [(71, Pc JUMPDEST), (72, Info CALLVALUE), (73, Arith ISZERO), (74, Stack (PUSH_N [81]))], Jumpi),
       (77, [(77, Stack (PUSH_N [0])), (79, Dup 1), (80, Unknown 253)], Next),
       (81, [(81, Pc JUMPDEST), (82, Stack (PUSH_N [101])), (84, Stack (PUSH_N [4])), (86, Dup 1), (87, Dup 1),
             (88, Stack CALLDATALOAD), (89, Swap 1), (90, Stack (PUSH_N [32])), (92, Arith ADD), (93, Swap 1),
             (94, Swap 2), (95, Swap 1), (96, Stack POP), (97, Stack POP), (98, Stack (PUSH_N [161]))],
        Jump),
       (101, [(101, Pc JUMPDEST), (102, Stack (PUSH_N [64])), (104, Memory MLOAD), (105, Dup 1), (106, Dup 3),
              (107, Dup 2), (108, Memory MSTORE), (109, Stack (PUSH_N [32])), (111, Arith ADD), (112, Swap 2),
              (113, Stack POP), (114, Stack POP), (115, Stack (PUSH_N [64])), (117, Memory MLOAD),
              (118, Dup 1), (119, Swap 2), (120, Arith SUB), (121, Swap 1), (122, Misc RETURN)],
        No),
       (123, [(123, Pc JUMPDEST), (124, Info CALLVALUE), (125, Arith ISZERO), (126, Stack (PUSH_N [133]))],
        Jumpi),
       (129, [(129, Stack (PUSH_N [0])), (131, Dup 1), (132, Unknown 253)], Next),
       (133, [(133, Pc JUMPDEST), (134, Stack (PUSH_N [139])), (136, Stack (PUSH_N [173]))], Jump),
       (139, [(139, Pc JUMPDEST), (140, Stack (PUSH_N [64])), (142, Memory MLOAD), (143, Dup 1), (144, Dup 3),
              (145, Dup 2), (146, Memory MSTORE), (147, Stack (PUSH_N [32])), (149, Arith ADD), (150, Swap 2),
              (151, Stack POP), (152, Stack POP), (153, Stack (PUSH_N [64])), (155, Memory MLOAD),
              (156, Dup 1), (157, Swap 2), (158, Arith SUB), (159, Swap 1), (160, Misc RETURN)],
        No),
       (161, [(161, Pc JUMPDEST), (162, Stack (PUSH_N [0])), (164, Stack (PUSH_N [1])), (166, Swap 1),
              (167, Stack POP)],
        Next),
       (168, [(168, Pc JUMPDEST), (169, Swap 2), (170, Swap 1), (171, Stack POP)], Jump),
       (173, [(173, Pc JUMPDEST), (174, Stack (PUSH_N [0])), (176, Stack (PUSH_N [2])), (178, Swap 1),
              (179, Stack POP)],
        Next),
       (180, [(180, Pc JUMPDEST), (181, Swap 1)], Jump), (183, [(183, Misc STOP)], No),
       (184, [(184, Log LOG1), (185, Stack (PUSH_N [98, 122, 122, 114, 48, 88])), (192, Arith SHA3),
              (193, Unknown 201), (194, Unknown 207), (195, Unknown 30), (196, Swap 14), (197, Dup 4),
              (198, Stack (PUSH_N
                            [31, 111, 154, 254, 206, 166, 43, 126, 134, 141, 152, 80, 46, 232, 85, 109, 202,
                             246, 171])),
              (218, Unknown 178), (219, Unknown 74), (220, Unknown 203), (221, Dup 12), (222, Unknown 192),
              (223, Unknown 217), (224, Unknown 251), (225, Misc STOP)],
        No),
       (226, [(226, Unknown 41)], Next)]\<rparr>"

lemma
"triple_blocks blocks (initial_state ** (data_lst dispatch1_hash) ** sent_value 0) (action (ContractReturn (word_rsplit (1:: w256))))"
apply (simp add: blocks_def)

sorry
typ "256 word \<Rightarrow> (byte list \<Rightarrow> byte list)"
lemma
"triple_blocks blocks (initial_state ** (data_lst dispatch_hash) ** ( if dispatch_hash = dispatch1_hash then (data_lst dispatch_hash) else emp) ** sent_value 0) 
( if dispatch_hash = dispatch1_hash then action (ContractReturn (word_rsplit (1:: w256))) else ())"
apply (simp add: blocks_def)


end