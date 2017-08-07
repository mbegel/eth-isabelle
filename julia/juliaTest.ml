
open Julia
open Parsr
open Lexr

open Lexing
open Printf

(* The following two functions comes from
 * https://github.com/realworldocaml/examples/tree/master/code/parsing-test
 * which is under UNLICENSE
 *)
let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parsr.main Lexr.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    exit (-1)
  | Parsr.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)
  | a ->
    raise a

let rec value_to_string = function
 | FalseV -> "false"
 | TrueV -> "true"
 | IntV i -> Z.to_string i
 | StringV i -> "'" ^ Z.to_string i ^ "'"
 | ListV lst -> "[" ^ String.concat "," (List.map value_to_string lst) ^ "]"
 | FunctionV (id, _, _, _) -> "function " ^ Z.to_string id

let print_state l =
  Pmap.iter (fun k v -> prerr_endline (Z.to_string k ^ " -> " ^ value_to_string v)) l 

let rec do_calc l = function
 | st :: lst ->
    let l = match Julia.eval_statement () l st 100 with
     | None -> prerr_endline "<error>"; l
     | Some (_,l,_) -> print_state l; prerr_endline "<step>"; l in
    do_calc l lst
 | [] -> prerr_endline "Exiting ..."

let main () =
  if Array.length Sys.argv < 2 then prerr_endline "need filename" else
  let lexbuf = Lexing.from_channel (open_in Sys.argv.(1)) in
  let lst = parse_with_error lexbuf in
  let _ = Printf.printf "Finished parsing.\n" in
  do_calc Julia.initial lst

let _ = main ()

