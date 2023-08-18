open StaticEnv
open Types

let solve_constraint (unifier : mono_type -> mono_type -> (unit, TypeError.unification_error) result) ((_, con) : mono_type_constraint) : (unit, TypeError.type_error) result =
  match con with
  | ConstraintEqual(lhs, rhs) ->
      unifier lhs rhs
      |> Result.map_error (fun uerr -> TypeError.TypeUnificationError(lhs, rhs, uerr))
  | ConstraintIdentity ->
      Ok(())


let try_constraint (con : mono_type_constraint) : (unit, TypeError.type_error) result =
  (* TED: JUST FOR DEBUG START *)
  let () =
    Printf.printf "trying %s ... " (Display.show_mono_type_constraint con);
  in
  (* TED: JUST FOR DEBUG END*)
  let unimap = UnificationMap.freeze () in
  let unirowmap = UnificationRowMap.freeze () in
  let result = solve_constraint Unification.unify_type_ted con in
  result
  |> Result.map (fun r ->
    Printf.printf "ok\n";
    r
  )
  |> Result.map_error (fun err ->
    Printf.printf "failed\n";
    UnificationRowMap.restore unirowmap;
    UnificationMap.restore unimap;
    err
  )


let apply_substituion (subst : mono_type_substitution) (subst_row : mono_row_substitution) ((range, con) : poly_type_constraint) : mono_type_constraint =
  match con with
  | ConstraintEqual(lhs, rhs) ->
      let lhs = lhs |> TypeConv.instantiate_by_map_ted subst subst_row in
      let rhs = rhs |> TypeConv.instantiate_by_map_ted subst subst_row in
      (range, ConstraintEqual(lhs, rhs))
  | ConstraintIdentity ->
      (range, ConstraintIdentity)


let resolve_constraint_reference (selected_map : poly_type_constraint TypeConstraintIDMap.t) (cref : mono_type_constraint_reference) : mono_type_constraint =
  match cref with
  | ConstraintRef(subst, subst_row, tcid) ->
      match selected_map |> TypeConstraintIDMap.find_opt tcid with
      | Some(con) -> con |> apply_substituion subst subst_row
      | None ->
          (* TED: JUST FOR DEBUG START *)
          let () =
            Printf.printf "constraint reference:\n";
            Printf.printf "[%s]\n" (cref |> Display.show_mono_type_constraint_reference);
            Printf.printf "selection map:\n";
            Printf.printf "[%s]\n" (selected_map |> TypeConstraintIDMap.bindings |> List.map (fun (id, sel) -> Printf.sprintf "%s -> %s" (TypeConstraintID.show id) (Display.show_poly_type_constraint sel)) |> String.concat ", ");
          in
          (* TED: JUST FOR DEBUG END*)
          assert false


let select_constraints (smap : poly_type_constraint_selection_map) (change_count : int) : (poly_type_constraint TypeConstraintIDMap.t * type_constraint_attribute list) list =
  let rec aux n xs =
    match xs with
    | [] -> [([], [])]
    | (tcid, (_, ConstraintSelection(con, alts))) :: rest ->
        let use_default =
          if List.length rest + 1 <= n then
            []
          else
            aux n rest |> List.map (fun (cons, attrs) -> ((tcid, con) :: cons, attrs))
        in
        let use_alts =
          if n = 0 then
            []
          else
            aux (n - 1) rest |> List.concat_map (fun (cons, attrs) ->
              alts |> List.map (fun alt ->
                match alt with
                | (_, ConstraintBranch(con, attr)) -> ((tcid, con) :: cons, attr :: attrs)
                | (r, ConstraintBranchAny(attr)) -> ((tcid, (r, ConstraintIdentity)) :: cons, attr :: attrs)
              )
            )
        in
        use_default @ use_alts
  in
  let candidates = aux change_count (smap |> TypeConstraintIDMap.bindings) in
  candidates |> List.map (fun (cons, attrs) -> (cons |> List.to_seq |> TypeConstraintIDMap.of_seq, attrs))


let select_default_constraints (smap : poly_type_constraint_selection_map) : poly_type_constraint TypeConstraintIDMap.t =
  match select_constraints smap 0 with
  | [(selected_map, _)] -> selected_map
  | _ -> assert false


let try_solving (crefs : mono_type_constraint_reference list) (smap : poly_type_constraint_selection_map) : (unit, TypeError.type_error) result =
  let open ResultMonad in
  if List.length crefs = 0 then
    return ()
  else
    let try_with_map selected_map =
      let unimap = UnificationMap.freeze () in
      let unirowmap = UnificationRowMap.freeze () in
      let cons = crefs |> List.map (resolve_constraint_reference selected_map) in
      let res = cons |> mapM try_constraint in
      UnificationRowMap.restore unirowmap;
      UnificationMap.restore unimap;
      res
    in
    let try_alternatives original_error change_count =
      let patterns = select_constraints smap change_count in
      let* _ = patterns |> mapM (fun (selected_map, attrs) ->
        match try_with_map selected_map with
        | Ok(_) ->
            (* This fix actually eliminated the type error. *)
            err @@ TypeError.ConstraintError(attrs, original_error)
        | Error(_) ->
            (* The error remains, so try other candidate fixes. *)
            return ()
      ) in
      return ()
    in
    (* We first check the default constraints are satisfiable. If it fails, try alternative constraints. *)
    Printf.printf " ---- ---- (try solving) ---- ----\n";
    match try_with_map (select_default_constraints smap) with
    | Ok(_) ->
        Printf.printf "OK\n";
        return ()
    | Error(e) ->
        Printf.printf " ---- - (try alternatives) -- ----\n";
        let* () = try_alternatives e 1 in
        (* None of the candidate fixes could correct the type error, so the original error is returned. *)
        err e


let apply_constraints_mono (crefs : mono_type_constraint_reference list) (smap : poly_type_constraint_selection_map) : (unit, TypeError.type_error) result =
  let open ResultMonad in
  let selected_map = select_default_constraints smap in
  let cons = crefs |> List.map (resolve_constraint_reference selected_map) in
  let* _ = cons |> mapM (solve_constraint Unification.unify_type) in
  return ()


let apply_constraints_poly (lev : level) (qtfbl : quantifiability) (additional_smap : poly_type_constraint_selection_map) (pty : poly_type) : (poly_type, TypeError.type_error) result =
  let open ResultMonad in
  match pty with
  | Poly(_, [], []) -> return pty
  | _ ->
      let (mty, crefs, smap) = TypeConv.instantiate (Level.succ lev) qtfbl pty in
      let* () = apply_constraints_mono crefs (TypeConstraintIDMap.merge smap additional_smap) in
      let pty = TypeConv.generalize lev mty [] [] in
      return pty

  
let apply_constraints_ssig (additional_map : poly_type_constraint_selection_map) (ssig : StructSig.t) : (StructSig.t, TypeError.type_error) result =
  let open ResultMonad in
  ssig |> StructSig.mapM
    ~v:(fun _ ventry ->
      let* val_type = apply_constraints_poly Level.bottom Quantifiable additional_map ventry.val_type in
      (* TED: JUST FOR DEBUG START *)
      let () =
        match ventry.val_type with
        | Poly(_, [], []) -> ()
        | _ ->
            Printf.printf "from: %s, to: %s\n" (Display.show_poly_type ventry.val_type) (Display.show_poly_type val_type)
      in
      (* TED: JUST FOR DEBUG END *)
      return { ventry with val_type = val_type }
    )
    ~a:(fun _ mentry -> return mentry)
    ~c:(fun _ centry -> return centry)
    ~f:(fun _ pt -> return pt)
    ~t:(fun _ tentry -> return tentry)
    ~m:(fun _ mentry -> return mentry)
    ~s:(fun _ absmodsig -> return absmodsig)
