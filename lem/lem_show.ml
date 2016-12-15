(*Generated by Lem from show.lem.*)


open Lem_string
open Lem_maybe
open Lem_num
open Lem_basic_classes

type 'a show_class={
  show_method: 'a -> string
}

let instance_Show_Show_string_dict:(string)show_class= ({

  show_method = (fun s->"\"" ^ (s ^ "\""))})

(*val stringFromMaybe : forall 'a. ('a -> string) -> maybe 'a -> string*)
let stringFromMaybe showX x:string=  
 ((match x with
    | Some x -> "Just (" ^ (showX x ^ ")")
    | None -> "Nothing"
  ))

let instance_Show_Show_Maybe_maybe_dict dict_Show_Show_a:('a option)show_class= ({

  show_method = (fun x_opt->stringFromMaybe  
  dict_Show_Show_a.show_method x_opt)})

(*val stringFromListAux : forall 'a. ('a -> string) -> list 'a -> string*)
let rec stringFromListAux showX x:string=  
 ((match x with
    | [] -> ""
    | x::xs' ->
      (match xs' with
      | [] -> showX x
      | _ -> showX x ^ ("; " ^ stringFromListAux showX xs')
      )
  ))

(*val stringFromList : forall 'a. ('a -> string) -> list 'a -> string*)
let stringFromList showX xs:string=  
 ("[" ^ (stringFromListAux showX xs ^ "]"))

let instance_Show_Show_list_dict dict_Show_Show_a:('a list)show_class= ({

  show_method = (fun xs->stringFromList  
  dict_Show_Show_a.show_method xs)})

(*val stringFromPair : forall 'a 'b. ('a -> string) -> ('b -> string) -> ('a * 'b) -> string*)
let stringFromPair showX showY (x,y):string=  
 ("(" ^ (showX x ^ (", " ^ (showY y ^ ")"))))

let instance_Show_Show_tup2_dict dict_Show_Show_a dict_Show_Show_b:('a*'b)show_class= ({

  show_method = (stringFromPair  
  dict_Show_Show_a.show_method  dict_Show_Show_b.show_method)})

let instance_Show_Show_bool_dict:(bool)show_class= ({

  show_method = (fun b->if b then "true" else "false")})
