open Pomap
open Context
open Block
open Blockmap
open Utils
open Zzdatatype.Datatype
open Language.FrontendTyped
open Typing.Termcheck
open Frontend_opt.To_typectx
open Language

type rty = Nt.t Language.rty

module Extraction = struct
  module BlockSet = BlockMap.BlockSet

  (* https://codereview.stackexchange.com/questions/40366/combinations-of-size-k-from-a-list-in-ocaml
    *)
  let rec combnk k lst =
    if k = 0 then [ [] ]
    else
      let rec inner = function
        | [] -> []
        | x :: xs -> List.map (fun z -> x :: z) (combnk (k - 1) xs) :: inner xs
      in
      List.concat (inner lst)

  (* Helper function to get the current rty of terms under consideration *)
  (* let unioned_rty_type3 (l : (LocalCtx.t * Block.t) list) : Block.t * _ =
     assert (not (List.is_empty l));
     let blocks = List.map snd l in
     let ids, lctx, newly_created_ids = Block.combine_all_args blocks in

     let nty = List.first l |> snd |> Block.to_nty in

     let unioned_rty =
       List.map (fun id -> Typectx.get_opt lctx id.x |> Option.get) ids
       |> union_rtys
     in

     let (Typectx l) = lctx in
     let lctx =
       Typectx
         (List.filter
            (fun { x; ty } -> not (List.mem x #: (erase_rty ty) ids))
            l)
     in

     let unioned_name = Rename.name () in
     let id = unioned_name #: nty in

     (* We should never actually try to use this thing *)
     Tracking.NameTracking.add_ast id Term.CErr #: nty;

     let unioned_block : Block.t =
       {
         id;
         ty = unioned_rty;
         lc = LocalCtx.add_name_to_ctx lctx unioned_name #: unioned_rty;
         cost = max_cost;
       }
     in

     let cleanup_func () =
       List.iter (LocalCtx.cleanup ~recursive:false) newly_created_ids
     in

     (unioned_block, cleanup_func) *)

  (* (* Helper function to get the current rty of terms under consideration *)
     let unioned_rty_type2 (l : (LocalCtx.t * BlockSet.t * Block.t * Ptset.t) list)
         : Block.t * _ =
       unioned_rty_type3 (List.map (fun (lc, _, b, _) -> (lc, b)) l) *)

  let e_unioned_rty_type2
      (l : (LocalCtx.t * BlockSet.t * Block.t * Ptset.t) list) : rty =
    List.map (fun (lc, _, b, _) -> (Block.existentialize b).ty) l |> union_rtys

  let e_unioned_rty_type3 (l : (LocalCtx.t * Block.t) list) : rty =
    List.map (fun (lc, b) -> (Block.existentialize b).ty) l |> union_rtys

  let extraction_is_sub_check lrtys target_block =
    let uctx = Context.get_global_uctx () in
    Typing.Termcheck.sub_rty_bool uctx
      (e_unioned_rty_type2 lrtys, (Block.existentialize target_block).ty)

  let extraction_is_sub_check_b lrtys target_block =
    let uctx = Context.get_global_uctx () in
    Typing.Termcheck.sub_rty_bool uctx
      (e_unioned_rty_type3 lrtys, (Block.existentialize target_block).ty)

  (* Try to find the largest block that can be removed *)
  let minimize_once (x : (LocalCtx.t * Block.t) list) (target_block : Block.t) :
      (LocalCtx.t * Block.t) list =
    print_endline "Minimize once";
    if List.length x = 1 then x
    else
      let () = assert (List.length x > 1) in

      print_endline "Target Block";
      print_endline (Block.layout target_block);

      (* let current_min = unioned_rty_type3 x in *)
      let current_min_block = e_unioned_rty_type3 x in

      (* print_endline "Current Min";
         print_endline (Block.layout current_min_block); *)

      (* Assert that current min passes subtyping check *)
      assert (extraction_is_sub_check_b x target_block);

      let res =
        List.fold_left
          (fun (current_block, current_list) proposed_list ->
            let proposed_min_block = e_unioned_rty_type3 proposed_list in
            (* print_endline "Proposed Min";
               print_endline (Block.layout proposed_min_block); *)
            if
              (* The proposed min implies the target*)
              extraction_is_sub_check_b proposed_list target_block
              &&
              (* And it is implied by the current min*)
              let uctx = Context.get_global_uctx () in
              Typing.Termcheck.sub_rty_bool uctx
                (current_min_block, proposed_min_block)
            then (
              print_endline "Proposed Min is better";

              (proposed_min_block, proposed_list))
            else (
              print_endline "Proposed Min is not better";

              (current_block, current_list)))
          (current_min_block, x)
          (combnk (List.length x - 1) x)
        |> snd
      in

      (* Assert that the result is still actually a solution *)
      assert (
          extraction_is_sub_check_b res target_block
      );

      res

  (* Repeat trying to reduce the number of blocks until minimum is found *)
  let minimize_num (x : (LocalCtx.t * Block.t) list) (target_block : Block.t) :
      (LocalCtx.t * Block.t) list =
    let rec aux (x : _ list) =
      let new_x = minimize_once x target_block in
      if List.length new_x < List.length x then aux new_x else new_x
    in
    aux x

  let rec minimize_type_helper (lc : LocalCtx.t) (map : BlockSet.t)
      (target_block : Block.t) (acc : 'a list) (remaining_set : Ptset.t)
      (current_minimum : 'b) : ('b * 'a list) option =
    print_endline "Minimize Type Helper";
    if Ptset.is_empty remaining_set then (
      print_endline "Done minimizing Type";
      None)
    else
      let idx = Ptset.choose remaining_set in
      let remaining_set = Ptset.remove idx remaining_set in
      let new_term = BlockSet.get_idx map idx in

      print_endline "Term to consider";
      print_endline (Block.layout new_term);

      (*       let id, rty = new_term in *)
      let new_thing : LocalCtx.t * BlockSet.t * Block.t * Ptset.t =
        (lc, map, new_term, BlockSet.get_preds map new_term)
      in

      let new_covered = new_thing :: acc in

      let new_covered_block = e_unioned_rty_type2 new_covered in

      (* print_endline "New Covered Block";
         print_endline (Block.layout new_covered_block); *)
      let uctx = Context.get_global_uctx () in

      if extraction_is_sub_check new_covered target_block then
        if
          (* print_endline "Covered was sub-type of target"; *)
          Typing.Termcheck.sub_rty_bool uctx (current_minimum, new_covered_block)
        then
          (* print_endline "Covered was super-type of current minimum"; *)
          Some (new_covered_block, new_thing :: acc)
        else
          (* print_endline "Covered was not super-type of current minimum"; *)
          minimize_type_helper lc map target_block acc remaining_set
            current_minimum
      else
        (* print_endline "Covered was not sub-type of target"; *)
        (* Other successors to draw on if not sufficient in hitting the target
           type *)
        minimize_type_helper lc map target_block (new_thing :: acc)
          remaining_set current_minimum

  (* Try to reduce coverage of a specific term*)
  let minimize_type (x : (LocalCtx.t * BlockSet.t * Block.t * Ptset.t) list)
      (target_ty_block : Block.t) :
      (LocalCtx.t * BlockSet.t * Block.t * Ptset.t) list =
    let current_coverage_block = e_unioned_rty_type2 x in

    assert (extraction_is_sub_check x target_ty_block);

    let res =
      List.fold_left
        (fun ((current_min_coverage : 'a), (acc : _ list)) (idx : int) :
             ('a * _ list) ->
          let current_term, rest_terms =
            Core.List.drop x idx |> List.destruct_opt |> Option.get
          in

          let lc, map, _, ptset = current_term in

          if Ptset.is_empty ptset then
            (* Bail out if there are no other possible options*)
            ( current_min_coverage,
              (* List.concat [ acc; [ current_term ]; rest_terms ]  *)
              current_term :: acc )
          else
            match
              minimize_type_helper lc map target_ty_block
                (List.concat [ acc; rest_terms ])
                ptset current_min_coverage
            with
            | None -> (current_min_coverage, current_term :: acc)
            | Some x -> x)
        (current_coverage_block, [])
        (range (List.length x))
      |> snd
    in

    assert (extraction_is_sub_check res target_ty_block);

    res

  (* Path/context agnostic checking against a type *)
  let check_types_against_target (tys : Block.t list)
      (target_ty : ExistentializedBlock.t) : bool =
    let uctx = !global_uctx |> Option.get in
    let eblocks = List.map (fun b -> (Block.existentialize b).ty) tys in

    sub_rty_bool uctx (union_rtys eblocks, target_ty.ty)

  let pset_is_sufficient_coverage (map : BlockSet.t) (pset : Ptset.t)
      (target_ty_block : Block.t) : bool =
    let block_candidates =
      Ptset.fold
        (fun idx acc ->
          let b = BlockSet.get_idx map idx in
          print_endline "current block";
          Block.layout b |> print_endline;
          b :: acc)
        pset []
    in
    if List.is_empty block_candidates then false
    else
      check_types_against_target block_candidates
        (Block.existentialize target_ty_block)

  (* Try to increase the coverage of a specific term to satisfy
     the target type *)
  let setup_type
      ((lc, map, (current_block, under_set)) :
        LocalCtx.t * BlockSet.t * (Block.t option * Ptset.t))
      (target_block : Block.t) :
      (LocalCtx.t * BlockSet.t * Block.t * Ptset.t) list =
    print_endline "Setup type";

    (* print_endline (layout_rty target_ty); *)
    let res =
      match current_block with
      | Some i ->
          print_endline "This block";
          [ (lc, map, i, under_set) ]
      | None ->
          Ptset.fold
            (fun idx acc ->
              let b = BlockSet.get_idx map idx in
              let p = BlockSet.get_preds map b in
              print_endline "current block";
              Block.layout b |> print_endline;

              print_endline "Printing Preds";
              BlockSet.print_ptset map p;
              (lc, map, b, p) :: acc)
            under_set []
    in

    assert (not (List.is_empty res));

    if not (extraction_is_sub_check res target_block) then (
      List.iter
        (fun (lc, _, eb, _) ->
          LocalCtx.layout lc |> print_endline;
          Block.layout eb |> print_endline)
        res;

      failwith "Setup_type does not have enough");

    res

  (** Lets try and simplify the extraction process by only considering one path
    at a time *)
  let extract_for_path (lc : LocalCtx.t) (target_path_block : Block.t)
      (bset : BlockSet.t) : (LocalCtx.t * Block.t) list =
    Printf.printf
      "\n\n Extracting from path-specific collections we are interested in\n";

    print_endline "Target block";
    Block.layout target_path_block |> print_endline;

    (let set = BlockSet.add_block bset target_path_block in
     Printf.printf "Path Specific Collection: %s\n"
       (layout_typectx layout_rty lc);
     BlockSet.print set);

    (* Does the target exist in this path? *)
    match BlockSet.find_block_opt bset target_path_block with
    | Some b ->
        (* Yes: Return current bs, no preds, and the target_block *)
        print_endline "Have a complete block for a path solution";
        (lc, b) :: []
    | None ->
        (* No: Return a new bs with the target block, any preds, and
           possibly a starting block from the succs *)
        let bs = BlockSet.add_block bset target_path_block in
        let p = BlockSet.get_preds bs target_path_block in
        let s = BlockSet.get_succs bs target_path_block in
        BlockSet.print_ptset bs p;

        (* Smallest block that covers the target fully *)
        (* let b =
             Ptset.min_elt_opt s
             |> Option.map (fun idx -> BlockSetE.get_idx bs idx)
           in

           (print_endline "Have a partial solution: ";
            match b with
            | Some b -> print_endline (ExistentializedBlock.layout b)
            | None -> print_endline "None"); *)
        (* TODO, we are going to avoid blocks that are too large for the moment *)
        let b = None in

        (* Some paths might not get blocks that aid in getting the
           target? *)
        if not (Ptset.is_empty p && Ptset.is_empty s) then
          if
            Option.is_none b
            && not (pset_is_sufficient_coverage bs p target_path_block)
          then (
            print_endline "return nothing2";
            [])
          else (
            print_endline "return a block";
            let starting_point = (lc, bs, (b, p)) in

            let block_choices = setup_type starting_point target_path_block in

            let block_choices = minimize_type block_choices target_path_block in

            List.iter
              (fun (lc, _, b, _) ->
                Pp.printf "Local Context: %s\n" (layout_typectx layout_rty lc);
                Pp.printf "Block:\n%s\n" (Block.layout b))
              block_choices;

            let block_choices =
              List.map (fun (lc, _, b, _) -> (lc, b)) block_choices
            in

            let block_choices = minimize_num block_choices target_path_block in

            (* When we are done, drop any remaining predesessors and the block
               map *)
            block_choices)
        else (
          print_endline "return nothing";
          [])
  (*
  (* Take blocks of different coverage types and join them together into full programs using non-deterministic choice *)
  let extract_blocks (collection : SynthesisCollection.t) (target_ty : rty) :
      (LocalCtx.t * Block.t) list =
    let target_nty = erase_rty target_ty in

    let target_block : Block.t =
      ExistentializedBlock.create_target target_ty
    in

    print_endline "Existentializing the general set";
    (* Get all blocks from the general collection *)
    let general_block_list =
      let ({ new_blocks; old_blocks } : BlockCollection.t) =
        collection.general_coll
      in

      List.append
        (BlockMap.existentialized_list new_blocks target_nty)
        (BlockMap.existentialized_list old_blocks target_nty)
    in

    let uctx = Context.get_global_uctx () in

    assert (Hashtbl.length collection.path_specific > 0);

    print_endline "Existentializing the path specific sets";
    Relations.clear_cache ();

    (* Get the sets for each path *)
    let path_specific_sets =
      Hashtbl.map
        (fun (lc, bc) ->
          LocalCtx.layout lc |> print_endline;
          ( lc,
            let ({ new_blocks; old_blocks } : BlockCollection.t) = bc in

            List.append
              (BlockMap.existentialized_list new_blocks target_nty)
              (BlockMap.existentialized_list old_blocks target_nty) ))
        collection.path_specific
    in

    (* We are going to do some normalization setup *)
    (* All General terms are going to get pushed into paths *)
    let path_specific_sets =
      Hashtbl.map
        (fun ((lc : LocalCtx.t), (path_blocks : _ list)) ->
          let res = BlockSetE.empty in
          (* TODO: We should only use this block once and enable caching *)
          (* Existentialization should rename the block... Maybe still worth
             it to clear cache lol just to not flood things*)
          let path_target_ty =
            ExistentializedBlock.path_promotion lc target_block
          in

          let conditional_add (bs : BlockSetE.t) (b : ExistentializedBlock.t) :
              BlockSetE.t =
            if ExistentializedBlock.is_sub_rty uctx b path_target_ty then
              BlockSetE.add_block bs b
            else if ExistentializedBlock.is_sub_rty uctx path_target_ty b then
              BlockSetE.add_block bs b
            else bs
          in

          (* Fold over general_terms for this path and path promote them *)
          let res =
            List.fold_left
              (fun acc b ->
                conditional_add acc (ExistentializedBlock.path_promotion lc b))
              res general_block_list
          in

          (* Fold over path specific terms for this path *)
          let res =
            List.fold_left (fun acc b -> conditional_add acc b) res path_blocks
          in

          (lc, (path_target_ty, res)))
        path_specific_sets
    in

    Printf.printf "\n\n Path Specific collections we are interested in\n";
    Hashtbl.iter
      (fun ctx (path_target_ty, set) ->
        let set = BlockSetE.add_block set path_target_ty in
        Printf.printf "Path Specific Collection: %s\n"
          (layout_typectx layout_rty ctx);
        BlockSetE.print set)
      path_specific_sets;

    let path_specific_sets_list =
      Hashtbl.to_seq path_specific_sets |> List.of_seq
    in

    let extracted_blocks =
      List.fold_left
        (fun acc (lc, (target_path_ty, set)) ->
          List.append acc (extract_for_existential_path lc target_path_ty set))
        [] path_specific_sets_list
    in

    minimize_num extracted_blocks target_ty *)
end
