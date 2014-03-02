open OUnit2;;
open Front;;
open XAST;;
open Positions;;
open Rewrite;;


let p = undefined_position

let string_function x = ASTio.to_string ASTio.XAST.pprint_expression x

let assert_equal_ast expected result = (fun test_ctxt ->
        assert_equal
                    ~msg:"process"
                    ~printer: (function l ->  (string_function l))
                    expected
                    (result))

let transform_calls =
  let create_term a b = (XAST.ELambda (p, (Name.Name "x", Types.TyVar (p, Name.TName "'a")),
                            XAST.EApp (p, a,b))) in
  let a = (XAST.EVar (p, Name.Name "hash", [Types.TyVar (p, Name.TName "'a")])) in
  let b = (XAST.EVar (p, Name.Name "x", [])) in
  let input = create_term a b in
  let newa = EApp(p, a, EVar(p, Name.Name "hashableX", [])) in
  let expected = create_term newa b in
  let record = { param_name = "hashableX"; to_rewrite = "hash" } in
  (assert_equal_ast expected (rewrite record input))


let suite =
  "suite">::: [ "transform_calls">:: transform_calls;
                "transform_calls">:: transform_calls;]
;;

let () =
    run_test_tt_main suite
;;
