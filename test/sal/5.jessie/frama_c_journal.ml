(* Frama-C journal generated at 09:35 the 09/07/2009 *)

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
 let () = Cmdline.Files.add "fr/test/sal/5.c" in
 let () = File.init_from_cmdline () in
 let () = Project.remove (Project.from_unique_name "temp") in
 let () = Project.set_current (Project.from_unique_name "jessie") in
 (* Finished *)
 Journal.finished ()

let () =
 try start ()
 with e -> Format.eprintf "Journal raised an exception: %s" (Printexc.to_string e)