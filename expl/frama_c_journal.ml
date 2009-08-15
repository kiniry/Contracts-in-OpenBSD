(* Frama-C journal generated at 10:15 the 11/08/2009 *)

(* Running *)
let start () =
 let () = Journal.run () in
 let () = Cmdline.Jessie.Analysis.set true in
 let () = Cmdline.SimplifyCfg.set true in
 let () = Cmdline.KeepSwitch.set true in
 let () = Cmdline.Constfold.set true in
 let () = Cmdline.PreprocessAnnot.set true in
 let () = Cmdline.CppExtraArgs.set
  (Cilutil.StringSet.add "-include e:\\Frama-C\\bin\\share\\frama-c\\jessie\\jessie_prolog.h" Cilutil.StringSet.empty) in
 let () = Cmdline.Jessie.Gui.set true in
 let () = Cmdline.Files.add "17d...c" in
 (* exception Sys_error("C:\\Users\\mstr-kul\\AppData\\Local\\Temp\\17d...cc5f5ee.i: No such file or directory") raised on: *)
 let __ : unit = File.init_from_cmdline () in
 (* Finished *)
 Journal.finished ()

let () =
 try start ()
 with e -> Format.eprintf "Journal raised an exception: %s" (Printexc.to_string e)