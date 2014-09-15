open Lexer
open List
open Printf

let rec print_res(l : (string * int) list)(total : int) : unit = 
	match l with
		[] -> printf "total - %d\n" total; ()
	| (name, n) :: l' -> (* printf "\n%s - %d" name n; *) print_res l' (total + n)

let _ = 
	let infile = open_in (Array.get Sys.argv 1) in
	let lexbuf = Lexing.from_channel infile in
  let l = Lexer.theorem [] lexbuf in
	print_res (rev l) 0
	

