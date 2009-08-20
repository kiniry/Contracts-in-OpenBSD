(* Frama-C journal generated at 08:46 the 20/08/2009 *)

(* Running *)
let start () =
 let () = Journal.run () in
 (* Finished *)
 Journal.finished ()

let () =
 try start ()
 with e -> Format.eprintf "Journal raised an exception: %s" (Printexc.to_string e)