
open MyUtil
open Types

type error =
  | MainModuleNameMismatch of {
      expected : module_name;
      got      : module_name;
    }
  | PackageDirectoryNotFound of string list
  | PackageReadingError of PackageReader.error
  | CyclicPackageDependency of (module_name * package_info) cycle
[@@deriving show { with_path = false }]

type 'a ok = ('a, error) result


module PackageDependencyGraph = DependencyGraph.Make(String)

type graph = package_info PackageDependencyGraph.t

type vertex = PackageDependencyGraph.Vertex.t


let rec add_package (graph : graph) ~prev:(vertex_prev_opt : vertex option) (main_module_name : module_name) : graph ok =
  let open ResultMonad in
  match graph |> PackageDependencyGraph.get_vertex main_module_name with
  | Some(vertex) ->
    (* If `main_module_name` has already been read: *)
      let graph =
        match vertex_prev_opt with
        | None ->
            graph

        | Some(vertex_prev) ->
            graph |> PackageDependencyGraph.add_edge ~from:vertex_prev ~to_:vertex
      in
      return graph

  | None ->
      Printf.printf "****PACKAGE: %s\n" main_module_name; (* TODO: remove this *)
      let* absdir =
        Config.resolve_package_directory main_module_name
          |> Result.map_error (fun cands -> PackageDirectoryNotFound(cands))
      in
      let* package =
        PackageReader.main absdir
          |> Result.map_error (fun e -> PackageReadingError(e))
      in
      if String.equal package.main_module_name main_module_name then
        let (graph, vertex) =
          match graph |> PackageDependencyGraph.add_vertex main_module_name package with
          | Error(_) -> assert false
          | Ok(pair) -> pair
        in
        let graph =
          match vertex_prev_opt with
          | None              -> graph
          | Some(vertex_prev) -> graph |> PackageDependencyGraph.add_edge ~from:vertex_prev ~to_:vertex
        in
        package.dependencies |> foldM (fun graph main_module_name_dep ->
          Printf.printf "****DEP2: %s ---> %s\n" main_module_name main_module_name_dep; (* TODO: remove this *)
          add_package graph ~prev:(Some(vertex)) main_module_name_dep
        ) graph
      else
        err @@ MainModuleNameMismatch{
          expected = main_module_name;
          got      = package.main_module_name;
        }


let main (package_name_set_init : PackageNameSet.t) : (package_info list) ok =
  let open ResultMonad in
  let main_module_names_init = package_name_set_init |> PackageNameSet.elements in
  let* graph =
    main_module_names_init |> foldM (fun graph main_module_name ->
      add_package graph ~prev:None main_module_name
    ) PackageDependencyGraph.empty
  in
  let* pairs =
    PackageDependencyGraph.topological_sort graph
      |> Result.map_error (fun cycle -> CyclicPackageDependency(cycle))
  in
  Printf.printf "****SORTED: %s\n" (pairs |> List.map (fun (n, _) -> n) |> String.concat " > "); (* TODO: remove this *)
  return (pairs |> List.map (fun (_, package) -> package))