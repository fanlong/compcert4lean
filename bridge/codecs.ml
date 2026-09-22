open Primitives

let rec enc_AST_typ (value : AST.typ) =
  match value with
  | AST.Tint ->
    node "Tint" []
  | AST.Tfloat ->
    node "Tfloat" []
  | AST.Tlong ->
    node "Tlong" []
  | AST.Tsingle ->
    node "Tsingle" []
  | AST.Tany32 ->
    node "Tany32" []
  | AST.Tany64 ->
    node "Tany64" []

and enc_AST_xtype (value : AST.xtype) =
  match value with
  | AST.Xbool ->
    node "Xbool" []
  | AST.Xint8signed ->
    node "Xint8signed" []
  | AST.Xint8unsigned ->
    node "Xint8unsigned" []
  | AST.Xint16signed ->
    node "Xint16signed" []
  | AST.Xint16unsigned ->
    node "Xint16unsigned" []
  | AST.Xint ->
    node "Xint" []
  | AST.Xfloat ->
    node "Xfloat" []
  | AST.Xlong ->
    node "Xlong" []
  | AST.Xsingle ->
    node "Xsingle" []
  | AST.Xptr ->
    node "Xptr" []
  | AST.Xany32 ->
    node "Xany32" []
  | AST.Xany64 ->
    node "Xany64" []
  | AST.Xvoid ->
    node "Xvoid" []

and enc_AST_calling_convention (value : AST.calling_convention) =
    node "AST_calling_convention" [(enc_option (enc_z)) value.cc_vararg; (enc_bool) value.cc_unproto; (enc_bool) value.cc_structret]

and enc_AST_signature (value : AST.signature) =
    node "AST_signature" [(enc_list (enc_AST_xtype)) value.sig_args; (enc_AST_xtype) value.sig_res; (enc_AST_calling_convention) value.sig_cc]

and enc_AST_memory_chunk (value : AST.memory_chunk) =
  match value with
  | AST.Mbool ->
    node "Mbool" []
  | AST.Mint8signed ->
    node "Mint8signed" []
  | AST.Mint8unsigned ->
    node "Mint8unsigned" []
  | AST.Mint16signed ->
    node "Mint16signed" []
  | AST.Mint16unsigned ->
    node "Mint16unsigned" []
  | AST.Mint32 ->
    node "Mint32" []
  | AST.Mint64 ->
    node "Mint64" []
  | AST.Mfloat32 ->
    node "Mfloat32" []
  | AST.Mfloat64 ->
    node "Mfloat64" []
  | AST.Many32 ->
    node "Many32" []
  | AST.Many64 ->
    node "Many64" []

and enc_AST_init_data (value : AST.init_data) =
  match value with
  | AST.Init_int8 (arg0) ->
    node "Init_int8" [(enc_int) arg0]
  | AST.Init_int16 (arg0) ->
    node "Init_int16" [(enc_int) arg0]
  | AST.Init_int32 (arg0) ->
    node "Init_int32" [(enc_int) arg0]
  | AST.Init_int64 (arg0) ->
    node "Init_int64" [(enc_long) arg0]
  | AST.Init_float32 (arg0) ->
    node "Init_float32" [(enc_single) arg0]
  | AST.Init_float64 (arg0) ->
    node "Init_float64" [(enc_float) arg0]
  | AST.Init_space (arg0) ->
    node "Init_space" [(enc_z) arg0]
  | AST.Init_addrof (arg0, arg1) ->
    node "Init_addrof" [(enc_pos) arg0; (enc_ptr) arg1]

and enc_AST_external_function (value : AST.external_function) =
  match value with
  | AST.EF_external (arg0, arg1) ->
    node "EF_external" [(enc_string) arg0; (enc_AST_signature) arg1]
  | AST.EF_builtin (arg0, arg1) ->
    node "EF_builtin" [(enc_string) arg0; (enc_AST_signature) arg1]
  | AST.EF_runtime (arg0, arg1) ->
    node "EF_runtime" [(enc_string) arg0; (enc_AST_signature) arg1]
  | AST.EF_vload (arg0) ->
    node "EF_vload" [(enc_AST_memory_chunk) arg0]
  | AST.EF_vstore (arg0) ->
    node "EF_vstore" [(enc_AST_memory_chunk) arg0]
  | AST.EF_malloc ->
    node "EF_malloc" []
  | AST.EF_free ->
    node "EF_free" []
  | AST.EF_memcpy (arg0, arg1) ->
    node "EF_memcpy" [(enc_z) arg0; (enc_z) arg1]
  | AST.EF_annot (arg0, arg1, arg2) ->
    node "EF_annot" [(enc_pos) arg0; (enc_string) arg1; (enc_list (enc_AST_typ)) arg2]
  | AST.EF_annot_val (arg0, arg1, arg2) ->
    node "EF_annot_val" [(enc_pos) arg0; (enc_string) arg1; (enc_AST_typ) arg2]
  | AST.EF_inline_asm (arg0, arg1, arg2) ->
    node "EF_inline_asm" [(enc_string) arg0; (enc_AST_signature) arg1; (enc_list (enc_string)) arg2]
  | AST.EF_debug (arg0, arg1, arg2) ->
    node "EF_debug" [(enc_pos) arg0; (enc_pos) arg1; (enc_list (enc_AST_typ)) arg2]

and enc_Ctypes_signedness (value : Ctypes.signedness) =
  match value with
  | Ctypes.Signed ->
    node "Signed" []
  | Ctypes.Unsigned ->
    node "Unsigned" []

and enc_Ctypes_intsize (value : Ctypes.intsize) =
  match value with
  | Ctypes.I8 ->
    node "I8" []
  | Ctypes.I16 ->
    node "I16" []
  | Ctypes.I32 ->
    node "I32" []
  | Ctypes.IBool ->
    node "IBool" []

and enc_Ctypes_floatsize (value : Ctypes.floatsize) =
  match value with
  | Ctypes.F32 ->
    node "F32" []
  | Ctypes.F64 ->
    node "F64" []

and enc_Ctypes_attr (value : Ctypes.attr) =
    node "Ctypes_attr" [(enc_bool) value.attr_volatile; (enc_option (enc_n)) value.attr_alignas]

and enc_Ctypes_coq_type (value : Ctypes.coq_type) =
  match value with
  | Ctypes.Tvoid ->
    node "Tvoid" []
  | Ctypes.Tint (arg0, arg1, arg2) ->
    node "Tint" [(enc_Ctypes_intsize) arg0; (enc_Ctypes_signedness) arg1; (enc_Ctypes_attr) arg2]
  | Ctypes.Tlong (arg0, arg1) ->
    node "Tlong" [(enc_Ctypes_signedness) arg0; (enc_Ctypes_attr) arg1]
  | Ctypes.Tfloat (arg0, arg1) ->
    node "Tfloat" [(enc_Ctypes_floatsize) arg0; (enc_Ctypes_attr) arg1]
  | Ctypes.Tpointer (arg0, arg1) ->
    node "Tpointer" [(enc_Ctypes_coq_type) arg0; (enc_Ctypes_attr) arg1]
  | Ctypes.Tarray (arg0, arg1, arg2) ->
    node "Tarray" [(enc_Ctypes_coq_type) arg0; (enc_z) arg1; (enc_Ctypes_attr) arg2]
  | Ctypes.Tfunction (arg0, arg1, arg2) ->
    node "Tfunction" [(enc_list (enc_Ctypes_coq_type)) arg0; (enc_Ctypes_coq_type) arg1; (enc_AST_calling_convention) arg2]
  | Ctypes.Tstruct (arg0, arg1) ->
    node "Tstruct" [(enc_pos) arg0; (enc_Ctypes_attr) arg1]
  | Ctypes.Tunion (arg0, arg1) ->
    node "Tunion" [(enc_pos) arg0; (enc_Ctypes_attr) arg1]

and enc_Ctypes_struct_or_union (value : Ctypes.struct_or_union) =
  match value with
  | Ctypes.Struct ->
    node "Struct" []
  | Ctypes.Union ->
    node "Union" []

and enc_Ctypes_member (value : Ctypes.member) =
  match value with
  | Ctypes.Member_plain (arg0, arg1) ->
    node "Member_plain" [(enc_pos) arg0; (enc_Ctypes_coq_type) arg1]
  | Ctypes.Member_bitfield (arg0, arg1, arg2, arg3, arg4, arg5) ->
    node "Member_bitfield" [(enc_pos) arg0; (enc_Ctypes_intsize) arg1; (enc_Ctypes_signedness) arg2; (enc_Ctypes_attr) arg3; (enc_z) arg4; (enc_bool) arg5]

and enc_Ctypes_composite_definition (value : Ctypes.composite_definition) =
  match value with
  | Ctypes.Composite (arg0, arg1, arg2, arg3) ->
    node "Composite" [(enc_pos) arg0; (enc_Ctypes_struct_or_union) arg1; (enc_list (enc_Ctypes_member)) arg2; (enc_Ctypes_attr) arg3]

and enc_Ctypes_bitfield (value : Ctypes.bitfield) =
  match value with
  | Ctypes.Full ->
    node "Full" []
  | Ctypes.Bits (arg0, arg1, arg2, arg3) ->
    node "Bits" [(enc_Ctypes_intsize) arg0; (enc_Ctypes_signedness) arg1; (enc_z) arg2; (enc_z) arg3]

and enc_Cop_unary_operation (value : Cop.unary_operation) =
  match value with
  | Cop.Onotbool ->
    node "Onotbool" []
  | Cop.Onotint ->
    node "Onotint" []
  | Cop.Oneg ->
    node "Oneg" []
  | Cop.Oabsfloat ->
    node "Oabsfloat" []

and enc_Cop_binary_operation (value : Cop.binary_operation) =
  match value with
  | Cop.Oadd ->
    node "Oadd" []
  | Cop.Osub ->
    node "Osub" []
  | Cop.Omul ->
    node "Omul" []
  | Cop.Odiv ->
    node "Odiv" []
  | Cop.Omod ->
    node "Omod" []
  | Cop.Oand ->
    node "Oand" []
  | Cop.Oor ->
    node "Oor" []
  | Cop.Oxor ->
    node "Oxor" []
  | Cop.Oshl ->
    node "Oshl" []
  | Cop.Oshr ->
    node "Oshr" []
  | Cop.Oeq ->
    node "Oeq" []
  | Cop.One ->
    node "One" []
  | Cop.Olt ->
    node "Olt" []
  | Cop.Ogt ->
    node "Ogt" []
  | Cop.Ole ->
    node "Ole" []
  | Cop.Oge ->
    node "Oge" []

and enc_Cop_incr_or_decr (value : Cop.incr_or_decr) =
  match value with
  | Cop.Incr ->
    node "Incr" []
  | Cop.Decr ->
    node "Decr" []

and enc_Values_coq_val (value : Values.coq_val) =
  match value with
  | Values.Vundef ->
    node "Vundef" []
  | Values.Vint (arg0) ->
    node "Vint" [(enc_int) arg0]
  | Values.Vlong (arg0) ->
    node "Vlong" [(enc_long) arg0]
  | Values.Vfloat (arg0) ->
    node "Vfloat" [(enc_float) arg0]
  | Values.Vsingle (arg0) ->
    node "Vsingle" [(enc_single) arg0]
  | Values.Vptr (arg0, arg1) ->
    node "Vptr" [(enc_pos) arg0; (enc_ptr) arg1]

and enc_Csyntax_expr (value : Csyntax.expr) =
  match value with
  | Csyntax.Eval (arg0, arg1) ->
    node "Eval" [(enc_Values_coq_val) arg0; (enc_Ctypes_coq_type) arg1]
  | Csyntax.Evar (arg0, arg1) ->
    node "Evar" [(enc_pos) arg0; (enc_Ctypes_coq_type) arg1]
  | Csyntax.Efield (arg0, arg1, arg2) ->
    node "Efield" [(enc_Csyntax_expr) arg0; (enc_pos) arg1; (enc_Ctypes_coq_type) arg2]
  | Csyntax.Evalof (arg0, arg1) ->
    node "Evalof" [(enc_Csyntax_expr) arg0; (enc_Ctypes_coq_type) arg1]
  | Csyntax.Ederef (arg0, arg1) ->
    node "Ederef" [(enc_Csyntax_expr) arg0; (enc_Ctypes_coq_type) arg1]
  | Csyntax.Eaddrof (arg0, arg1) ->
    node "Eaddrof" [(enc_Csyntax_expr) arg0; (enc_Ctypes_coq_type) arg1]
  | Csyntax.Eunop (arg0, arg1, arg2) ->
    node "Eunop" [(enc_Cop_unary_operation) arg0; (enc_Csyntax_expr) arg1; (enc_Ctypes_coq_type) arg2]
  | Csyntax.Ebinop (arg0, arg1, arg2, arg3) ->
    node "Ebinop" [(enc_Cop_binary_operation) arg0; (enc_Csyntax_expr) arg1; (enc_Csyntax_expr) arg2; (enc_Ctypes_coq_type) arg3]
  | Csyntax.Ecast (arg0, arg1) ->
    node "Ecast" [(enc_Csyntax_expr) arg0; (enc_Ctypes_coq_type) arg1]
  | Csyntax.Eseqand (arg0, arg1, arg2) ->
    node "Eseqand" [(enc_Csyntax_expr) arg0; (enc_Csyntax_expr) arg1; (enc_Ctypes_coq_type) arg2]
  | Csyntax.Eseqor (arg0, arg1, arg2) ->
    node "Eseqor" [(enc_Csyntax_expr) arg0; (enc_Csyntax_expr) arg1; (enc_Ctypes_coq_type) arg2]
  | Csyntax.Econdition (arg0, arg1, arg2, arg3) ->
    node "Econdition" [(enc_Csyntax_expr) arg0; (enc_Csyntax_expr) arg1; (enc_Csyntax_expr) arg2; (enc_Ctypes_coq_type) arg3]
  | Csyntax.Esizeof (arg0, arg1) ->
    node "Esizeof" [(enc_Ctypes_coq_type) arg0; (enc_Ctypes_coq_type) arg1]
  | Csyntax.Ealignof (arg0, arg1) ->
    node "Ealignof" [(enc_Ctypes_coq_type) arg0; (enc_Ctypes_coq_type) arg1]
  | Csyntax.Eassign (arg0, arg1, arg2) ->
    node "Eassign" [(enc_Csyntax_expr) arg0; (enc_Csyntax_expr) arg1; (enc_Ctypes_coq_type) arg2]
  | Csyntax.Eassignop (arg0, arg1, arg2, arg3, arg4) ->
    node "Eassignop" [(enc_Cop_binary_operation) arg0; (enc_Csyntax_expr) arg1; (enc_Csyntax_expr) arg2; (enc_Ctypes_coq_type) arg3; (enc_Ctypes_coq_type) arg4]
  | Csyntax.Epostincr (arg0, arg1, arg2) ->
    node "Epostincr" [(enc_Cop_incr_or_decr) arg0; (enc_Csyntax_expr) arg1; (enc_Ctypes_coq_type) arg2]
  | Csyntax.Ecomma (arg0, arg1, arg2) ->
    node "Ecomma" [(enc_Csyntax_expr) arg0; (enc_Csyntax_expr) arg1; (enc_Ctypes_coq_type) arg2]
  | Csyntax.Ecall (arg0, arg1, arg2) ->
    node "Ecall" [(enc_Csyntax_expr) arg0; (enc_Csyntax_exprlist) arg1; (enc_Ctypes_coq_type) arg2]
  | Csyntax.Ebuiltin (arg0, arg1, arg2, arg3) ->
    node "Ebuiltin" [(enc_AST_external_function) arg0; (enc_list (enc_Ctypes_coq_type)) arg1; (enc_Csyntax_exprlist) arg2; (enc_Ctypes_coq_type) arg3]
  | Csyntax.Eloc (arg0, arg1, arg2, arg3) ->
    node "Eloc" [(enc_pos) arg0; (enc_ptr) arg1; (enc_Ctypes_bitfield) arg2; (enc_Ctypes_coq_type) arg3]
  | Csyntax.Eparen (arg0, arg1, arg2) ->
    node "Eparen" [(enc_Csyntax_expr) arg0; (enc_Ctypes_coq_type) arg1; (enc_Ctypes_coq_type) arg2]

and enc_Csyntax_exprlist (value : Csyntax.exprlist) =
  match value with
  | Csyntax.Enil ->
    node "Enil" []
  | Csyntax.Econs (arg0, arg1) ->
    node "Econs" [(enc_Csyntax_expr) arg0; (enc_Csyntax_exprlist) arg1]

and enc_Csyntax_statement (value : Csyntax.statement) =
  match value with
  | Csyntax.Sskip ->
    node "Sskip" []
  | Csyntax.Sdo (arg0) ->
    node "Sdo" [(enc_Csyntax_expr) arg0]
  | Csyntax.Ssequence (arg0, arg1) ->
    node "Ssequence" [(enc_Csyntax_statement) arg0; (enc_Csyntax_statement) arg1]
  | Csyntax.Sifthenelse (arg0, arg1, arg2) ->
    node "Sifthenelse" [(enc_Csyntax_expr) arg0; (enc_Csyntax_statement) arg1; (enc_Csyntax_statement) arg2]
  | Csyntax.Swhile (arg0, arg1) ->
    node "Swhile" [(enc_Csyntax_expr) arg0; (enc_Csyntax_statement) arg1]
  | Csyntax.Sdowhile (arg0, arg1) ->
    node "Sdowhile" [(enc_Csyntax_expr) arg0; (enc_Csyntax_statement) arg1]
  | Csyntax.Sfor (arg0, arg1, arg2, arg3) ->
    node "Sfor" [(enc_Csyntax_statement) arg0; (enc_Csyntax_expr) arg1; (enc_Csyntax_statement) arg2; (enc_Csyntax_statement) arg3]
  | Csyntax.Sbreak ->
    node "Sbreak" []
  | Csyntax.Scontinue ->
    node "Scontinue" []
  | Csyntax.Sreturn (arg0) ->
    node "Sreturn" [(enc_option (enc_Csyntax_expr)) arg0]
  | Csyntax.Sswitch (arg0, arg1) ->
    node "Sswitch" [(enc_Csyntax_expr) arg0; (enc_Csyntax_labeled_statements) arg1]
  | Csyntax.Slabel (arg0, arg1) ->
    node "Slabel" [(enc_pos) arg0; (enc_Csyntax_statement) arg1]
  | Csyntax.Sgoto (arg0) ->
    node "Sgoto" [(enc_pos) arg0]

and enc_Csyntax_labeled_statements (value : Csyntax.labeled_statements) =
  match value with
  | Csyntax.LSnil ->
    node "LSnil" []
  | Csyntax.LScons (arg0, arg1, arg2) ->
    node "LScons" [(enc_option (enc_z)) arg0; (enc_Csyntax_statement) arg1; (enc_Csyntax_labeled_statements) arg2]

and enc_Csyntax_coq_function (value : Csyntax.coq_function) =
    node "Csyntax_coq_function" [(enc_Ctypes_coq_type) value.fn_return; (enc_AST_calling_convention) value.fn_callconv; (enc_list (enc_pair (enc_pos) (enc_Ctypes_coq_type))) value.fn_params; (enc_list (enc_pair (enc_pos) (enc_Ctypes_coq_type))) value.fn_vars; (enc_Csyntax_statement) value.fn_body]

and enc_Asm_ireg (value : Asm.ireg) =
  match value with
  | Asm.RAX ->
    node "RAX" []
  | Asm.RBX ->
    node "RBX" []
  | Asm.RCX ->
    node "RCX" []
  | Asm.RDX ->
    node "RDX" []
  | Asm.RSI ->
    node "RSI" []
  | Asm.RDI ->
    node "RDI" []
  | Asm.RBP ->
    node "RBP" []
  | Asm.RSP ->
    node "RSP" []
  | Asm.R8 ->
    node "R8" []
  | Asm.R9 ->
    node "R9" []
  | Asm.R10 ->
    node "R10" []
  | Asm.R11 ->
    node "R11" []
  | Asm.R12 ->
    node "R12" []
  | Asm.R13 ->
    node "R13" []
  | Asm.R14 ->
    node "R14" []
  | Asm.R15 ->
    node "R15" []

and enc_Asm_freg (value : Asm.freg) =
  match value with
  | Asm.XMM0 ->
    node "XMM0" []
  | Asm.XMM1 ->
    node "XMM1" []
  | Asm.XMM2 ->
    node "XMM2" []
  | Asm.XMM3 ->
    node "XMM3" []
  | Asm.XMM4 ->
    node "XMM4" []
  | Asm.XMM5 ->
    node "XMM5" []
  | Asm.XMM6 ->
    node "XMM6" []
  | Asm.XMM7 ->
    node "XMM7" []
  | Asm.XMM8 ->
    node "XMM8" []
  | Asm.XMM9 ->
    node "XMM9" []
  | Asm.XMM10 ->
    node "XMM10" []
  | Asm.XMM11 ->
    node "XMM11" []
  | Asm.XMM12 ->
    node "XMM12" []
  | Asm.XMM13 ->
    node "XMM13" []
  | Asm.XMM14 ->
    node "XMM14" []
  | Asm.XMM15 ->
    node "XMM15" []

and enc_Asm_crbit (value : Asm.crbit) =
  match value with
  | Asm.ZF ->
    node "ZF" []
  | Asm.CF ->
    node "CF" []
  | Asm.PF ->
    node "PF" []
  | Asm.SF ->
    node "SF" []
  | Asm.OF ->
    node "OF" []

and enc_Asm_preg (value : Asm.preg) =
  match value with
  | Asm.PC ->
    node "PC" []
  | Asm.IR (arg0) ->
    node "IR" [(enc_Asm_ireg) arg0]
  | Asm.FR (arg0) ->
    node "FR" [(enc_Asm_freg) arg0]
  | Asm.ST0 ->
    node "ST0" []
  | Asm.CR (arg0) ->
    node "CR" [(enc_Asm_crbit) arg0]
  | Asm.RA ->
    node "RA" []

and enc_Asm_addrmode (value : Asm.addrmode) =
  match value with
  | Asm.Addrmode (arg0, arg1, arg2) ->
    node "Addrmode" [(enc_option (enc_Asm_ireg)) arg0; (enc_option (enc_pair (enc_Asm_ireg) (enc_z))) arg1; (enc_sum (enc_z) (enc_pair (enc_pos) (enc_ptr))) arg2]

and enc_Asm_testcond (value : Asm.testcond) =
  match value with
  | Asm.Cond_e ->
    node "Cond_e" []
  | Asm.Cond_ne ->
    node "Cond_ne" []
  | Asm.Cond_b ->
    node "Cond_b" []
  | Asm.Cond_be ->
    node "Cond_be" []
  | Asm.Cond_ae ->
    node "Cond_ae" []
  | Asm.Cond_a ->
    node "Cond_a" []
  | Asm.Cond_l ->
    node "Cond_l" []
  | Asm.Cond_le ->
    node "Cond_le" []
  | Asm.Cond_ge ->
    node "Cond_ge" []
  | Asm.Cond_g ->
    node "Cond_g" []
  | Asm.Cond_p ->
    node "Cond_p" []
  | Asm.Cond_np ->
    node "Cond_np" []

and enc_Asm_instruction (value : Asm.instruction) =
  match value with
  | Asm.Pmov_rr (arg0, arg1) ->
    node "Pmov_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovl_ri (arg0, arg1) ->
    node "Pmovl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Pmovq_ri (arg0, arg1) ->
    node "Pmovq_ri" [(enc_Asm_ireg) arg0; (enc_long) arg1]
  | Asm.Pmov_rs (arg0, arg1) ->
    node "Pmov_rs" [(enc_Asm_ireg) arg0; (enc_pos) arg1]
  | Asm.Pmovl_rm (arg0, arg1) ->
    node "Pmovl_rm" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovq_rm (arg0, arg1) ->
    node "Pmovq_rm" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovl_mr (arg0, arg1) ->
    node "Pmovl_mr" [(enc_Asm_addrmode) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovq_mr (arg0, arg1) ->
    node "Pmovq_mr" [(enc_Asm_addrmode) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovsd_ff (arg0, arg1) ->
    node "Pmovsd_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pmovsd_fi (arg0, arg1) ->
    node "Pmovsd_fi" [(enc_Asm_freg) arg0; (enc_float) arg1]
  | Asm.Pmovsd_fm (arg0, arg1) ->
    node "Pmovsd_fm" [(enc_Asm_freg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovsd_mf (arg0, arg1) ->
    node "Pmovsd_mf" [(enc_Asm_addrmode) arg0; (enc_Asm_freg) arg1]
  | Asm.Pmovss_fi (arg0, arg1) ->
    node "Pmovss_fi" [(enc_Asm_freg) arg0; (enc_single) arg1]
  | Asm.Pmovss_fm (arg0, arg1) ->
    node "Pmovss_fm" [(enc_Asm_freg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovss_mf (arg0, arg1) ->
    node "Pmovss_mf" [(enc_Asm_addrmode) arg0; (enc_Asm_freg) arg1]
  | Asm.Pfldl_m (arg0) ->
    node "Pfldl_m" [(enc_Asm_addrmode) arg0]
  | Asm.Pfstpl_m (arg0) ->
    node "Pfstpl_m" [(enc_Asm_addrmode) arg0]
  | Asm.Pflds_m (arg0) ->
    node "Pflds_m" [(enc_Asm_addrmode) arg0]
  | Asm.Pfstps_m (arg0) ->
    node "Pfstps_m" [(enc_Asm_addrmode) arg0]
  | Asm.Pmovb_mr (arg0, arg1) ->
    node "Pmovb_mr" [(enc_Asm_addrmode) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovw_mr (arg0, arg1) ->
    node "Pmovw_mr" [(enc_Asm_addrmode) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovzb_rr (arg0, arg1) ->
    node "Pmovzb_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovzb_rm (arg0, arg1) ->
    node "Pmovzb_rm" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovsb_rr (arg0, arg1) ->
    node "Pmovsb_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovsb_rm (arg0, arg1) ->
    node "Pmovsb_rm" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovzw_rr (arg0, arg1) ->
    node "Pmovzw_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovzw_rm (arg0, arg1) ->
    node "Pmovzw_rm" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovsw_rr (arg0, arg1) ->
    node "Pmovsw_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovsw_rm (arg0, arg1) ->
    node "Pmovsw_rm" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovzl_rr (arg0, arg1) ->
    node "Pmovzl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovsl_rr (arg0, arg1) ->
    node "Pmovsl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovls_rr (arg0) ->
    node "Pmovls_rr" [(enc_Asm_ireg) arg0]
  | Asm.Pcvtsd2ss_ff (arg0, arg1) ->
    node "Pcvtsd2ss_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pcvtss2sd_ff (arg0, arg1) ->
    node "Pcvtss2sd_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pcvttsd2si_rf (arg0, arg1) ->
    node "Pcvttsd2si_rf" [(enc_Asm_ireg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pcvtsi2sd_fr (arg0, arg1) ->
    node "Pcvtsi2sd_fr" [(enc_Asm_freg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pcvttss2si_rf (arg0, arg1) ->
    node "Pcvttss2si_rf" [(enc_Asm_ireg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pcvtsi2ss_fr (arg0, arg1) ->
    node "Pcvtsi2ss_fr" [(enc_Asm_freg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pcvttsd2sl_rf (arg0, arg1) ->
    node "Pcvttsd2sl_rf" [(enc_Asm_ireg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pcvtsl2sd_fr (arg0, arg1) ->
    node "Pcvtsl2sd_fr" [(enc_Asm_freg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pcvttss2sl_rf (arg0, arg1) ->
    node "Pcvttss2sl_rf" [(enc_Asm_ireg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pcvtsl2ss_fr (arg0, arg1) ->
    node "Pcvtsl2ss_fr" [(enc_Asm_freg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pleal (arg0, arg1) ->
    node "Pleal" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pleaq (arg0, arg1) ->
    node "Pleaq" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pnegl (arg0) ->
    node "Pnegl" [(enc_Asm_ireg) arg0]
  | Asm.Pnegq (arg0) ->
    node "Pnegq" [(enc_Asm_ireg) arg0]
  | Asm.Paddl_ri (arg0, arg1) ->
    node "Paddl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Paddq_ri (arg0, arg1) ->
    node "Paddq_ri" [(enc_Asm_ireg) arg0; (enc_long) arg1]
  | Asm.Psubl_rr (arg0, arg1) ->
    node "Psubl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Psubq_rr (arg0, arg1) ->
    node "Psubq_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pimull_rr (arg0, arg1) ->
    node "Pimull_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pimulq_rr (arg0, arg1) ->
    node "Pimulq_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pimull_ri (arg0, arg1) ->
    node "Pimull_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Pimulq_ri (arg0, arg1) ->
    node "Pimulq_ri" [(enc_Asm_ireg) arg0; (enc_long) arg1]
  | Asm.Pimull_r (arg0) ->
    node "Pimull_r" [(enc_Asm_ireg) arg0]
  | Asm.Pimulq_r (arg0) ->
    node "Pimulq_r" [(enc_Asm_ireg) arg0]
  | Asm.Pmull_r (arg0) ->
    node "Pmull_r" [(enc_Asm_ireg) arg0]
  | Asm.Pmulq_r (arg0) ->
    node "Pmulq_r" [(enc_Asm_ireg) arg0]
  | Asm.Pcltd ->
    node "Pcltd" []
  | Asm.Pcqto ->
    node "Pcqto" []
  | Asm.Pdivl (arg0) ->
    node "Pdivl" [(enc_Asm_ireg) arg0]
  | Asm.Pdivq (arg0) ->
    node "Pdivq" [(enc_Asm_ireg) arg0]
  | Asm.Pidivl (arg0) ->
    node "Pidivl" [(enc_Asm_ireg) arg0]
  | Asm.Pidivq (arg0) ->
    node "Pidivq" [(enc_Asm_ireg) arg0]
  | Asm.Pandl_rr (arg0, arg1) ->
    node "Pandl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pandq_rr (arg0, arg1) ->
    node "Pandq_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pandl_ri (arg0, arg1) ->
    node "Pandl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Pandq_ri (arg0, arg1) ->
    node "Pandq_ri" [(enc_Asm_ireg) arg0; (enc_long) arg1]
  | Asm.Porl_rr (arg0, arg1) ->
    node "Porl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Porq_rr (arg0, arg1) ->
    node "Porq_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Porl_ri (arg0, arg1) ->
    node "Porl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Porq_ri (arg0, arg1) ->
    node "Porq_ri" [(enc_Asm_ireg) arg0; (enc_long) arg1]
  | Asm.Pxorl_r (arg0) ->
    node "Pxorl_r" [(enc_Asm_ireg) arg0]
  | Asm.Pxorq_r (arg0) ->
    node "Pxorq_r" [(enc_Asm_ireg) arg0]
  | Asm.Pxorl_rr (arg0, arg1) ->
    node "Pxorl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pxorq_rr (arg0, arg1) ->
    node "Pxorq_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pxorl_ri (arg0, arg1) ->
    node "Pxorl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Pxorq_ri (arg0, arg1) ->
    node "Pxorq_ri" [(enc_Asm_ireg) arg0; (enc_long) arg1]
  | Asm.Pnotl (arg0) ->
    node "Pnotl" [(enc_Asm_ireg) arg0]
  | Asm.Pnotq (arg0) ->
    node "Pnotq" [(enc_Asm_ireg) arg0]
  | Asm.Psall_rcl (arg0) ->
    node "Psall_rcl" [(enc_Asm_ireg) arg0]
  | Asm.Psalq_rcl (arg0) ->
    node "Psalq_rcl" [(enc_Asm_ireg) arg0]
  | Asm.Psall_ri (arg0, arg1) ->
    node "Psall_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Psalq_ri (arg0, arg1) ->
    node "Psalq_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Pshrl_rcl (arg0) ->
    node "Pshrl_rcl" [(enc_Asm_ireg) arg0]
  | Asm.Pshrq_rcl (arg0) ->
    node "Pshrq_rcl" [(enc_Asm_ireg) arg0]
  | Asm.Pshrl_ri (arg0, arg1) ->
    node "Pshrl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Pshrq_ri (arg0, arg1) ->
    node "Pshrq_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Psarl_rcl (arg0) ->
    node "Psarl_rcl" [(enc_Asm_ireg) arg0]
  | Asm.Psarq_rcl (arg0) ->
    node "Psarq_rcl" [(enc_Asm_ireg) arg0]
  | Asm.Psarl_ri (arg0, arg1) ->
    node "Psarl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Psarq_ri (arg0, arg1) ->
    node "Psarq_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Pshld_ri (arg0, arg1, arg2) ->
    node "Pshld_ri" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1; (enc_int) arg2]
  | Asm.Prorl_ri (arg0, arg1) ->
    node "Prorl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Prorq_ri (arg0, arg1) ->
    node "Prorq_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Pcmpl_rr (arg0, arg1) ->
    node "Pcmpl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pcmpq_rr (arg0, arg1) ->
    node "Pcmpq_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pcmpl_ri (arg0, arg1) ->
    node "Pcmpl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Pcmpq_ri (arg0, arg1) ->
    node "Pcmpq_ri" [(enc_Asm_ireg) arg0; (enc_long) arg1]
  | Asm.Ptestl_rr (arg0, arg1) ->
    node "Ptestl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Ptestq_rr (arg0, arg1) ->
    node "Ptestq_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Ptestl_ri (arg0, arg1) ->
    node "Ptestl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Ptestq_ri (arg0, arg1) ->
    node "Ptestq_ri" [(enc_Asm_ireg) arg0; (enc_long) arg1]
  | Asm.Pcmov (arg0, arg1, arg2) ->
    node "Pcmov" [(enc_Asm_testcond) arg0; (enc_Asm_ireg) arg1; (enc_Asm_ireg) arg2]
  | Asm.Psetcc (arg0, arg1) ->
    node "Psetcc" [(enc_Asm_testcond) arg0; (enc_Asm_ireg) arg1]
  | Asm.Paddd_ff (arg0, arg1) ->
    node "Paddd_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Psubd_ff (arg0, arg1) ->
    node "Psubd_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pmuld_ff (arg0, arg1) ->
    node "Pmuld_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pdivd_ff (arg0, arg1) ->
    node "Pdivd_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pnegd (arg0) ->
    node "Pnegd" [(enc_Asm_freg) arg0]
  | Asm.Pabsd (arg0) ->
    node "Pabsd" [(enc_Asm_freg) arg0]
  | Asm.Pcomisd_ff (arg0, arg1) ->
    node "Pcomisd_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pxorpd_f (arg0) ->
    node "Pxorpd_f" [(enc_Asm_freg) arg0]
  | Asm.Padds_ff (arg0, arg1) ->
    node "Padds_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Psubs_ff (arg0, arg1) ->
    node "Psubs_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pmuls_ff (arg0, arg1) ->
    node "Pmuls_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pdivs_ff (arg0, arg1) ->
    node "Pdivs_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pnegs (arg0) ->
    node "Pnegs" [(enc_Asm_freg) arg0]
  | Asm.Pabss (arg0) ->
    node "Pabss" [(enc_Asm_freg) arg0]
  | Asm.Pcomiss_ff (arg0, arg1) ->
    node "Pcomiss_ff" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pxorps_f (arg0) ->
    node "Pxorps_f" [(enc_Asm_freg) arg0]
  | Asm.Pjmp_l (arg0) ->
    node "Pjmp_l" [(enc_pos) arg0]
  | Asm.Pjmp_s (arg0, arg1) ->
    node "Pjmp_s" [(enc_pos) arg0; (enc_AST_signature) arg1]
  | Asm.Pjmp_r (arg0, arg1) ->
    node "Pjmp_r" [(enc_Asm_ireg) arg0; (enc_AST_signature) arg1]
  | Asm.Pjcc (arg0, arg1) ->
    node "Pjcc" [(enc_Asm_testcond) arg0; (enc_pos) arg1]
  | Asm.Pjcc2 (arg0, arg1, arg2) ->
    node "Pjcc2" [(enc_Asm_testcond) arg0; (enc_Asm_testcond) arg1; (enc_pos) arg2]
  | Asm.Pjmptbl (arg0, arg1) ->
    node "Pjmptbl" [(enc_Asm_ireg) arg0; (enc_list (enc_pos)) arg1]
  | Asm.Pcall_s (arg0, arg1) ->
    node "Pcall_s" [(enc_pos) arg0; (enc_AST_signature) arg1]
  | Asm.Pcall_r (arg0, arg1) ->
    node "Pcall_r" [(enc_Asm_ireg) arg0; (enc_AST_signature) arg1]
  | Asm.Pret ->
    node "Pret" []
  | Asm.Pmov_rm_a (arg0, arg1) ->
    node "Pmov_rm_a" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmov_mr_a (arg0, arg1) ->
    node "Pmov_mr_a" [(enc_Asm_addrmode) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pmovsd_fm_a (arg0, arg1) ->
    node "Pmovsd_fm_a" [(enc_Asm_freg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovsd_mf_a (arg0, arg1) ->
    node "Pmovsd_mf_a" [(enc_Asm_addrmode) arg0; (enc_Asm_freg) arg1]
  | Asm.Plabel (arg0) ->
    node "Plabel" [(enc_pos) arg0]
  | Asm.Pallocframe (arg0, arg1, arg2) ->
    node "Pallocframe" [(enc_z) arg0; (enc_ptr) arg1; (enc_ptr) arg2]
  | Asm.Pfreeframe (arg0, arg1, arg2) ->
    node "Pfreeframe" [(enc_z) arg0; (enc_ptr) arg1; (enc_ptr) arg2]
  | Asm.Pbuiltin (arg0, arg1, arg2) ->
    node "Pbuiltin" [(enc_AST_external_function) arg0; (enc_list (enc_A_builtin_arg)) arg1; (enc_A_builtin_res) arg2]
  | Asm.Padcl_ri (arg0, arg1) ->
    node "Padcl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Padcl_rr (arg0, arg1) ->
    node "Padcl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Paddl_mi (arg0, arg1) ->
    node "Paddl_mi" [(enc_Asm_addrmode) arg0; (enc_int) arg1]
  | Asm.Paddl_rr (arg0, arg1) ->
    node "Paddl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pbsfl (arg0, arg1) ->
    node "Pbsfl" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pbsfq (arg0, arg1) ->
    node "Pbsfq" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pbsrl (arg0, arg1) ->
    node "Pbsrl" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pbsrq (arg0, arg1) ->
    node "Pbsrq" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Pbswap64 (arg0) ->
    node "Pbswap64" [(enc_Asm_ireg) arg0]
  | Asm.Pbswap32 (arg0) ->
    node "Pbswap32" [(enc_Asm_ireg) arg0]
  | Asm.Pbswap16 (arg0) ->
    node "Pbswap16" [(enc_Asm_ireg) arg0]
  | Asm.Pcfi_adjust (arg0) ->
    node "Pcfi_adjust" [(enc_int) arg0]
  | Asm.Pfmadd132 (arg0, arg1, arg2) ->
    node "Pfmadd132" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfmadd213 (arg0, arg1, arg2) ->
    node "Pfmadd213" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfmadd231 (arg0, arg1, arg2) ->
    node "Pfmadd231" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfmsub132 (arg0, arg1, arg2) ->
    node "Pfmsub132" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfmsub213 (arg0, arg1, arg2) ->
    node "Pfmsub213" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfmsub231 (arg0, arg1, arg2) ->
    node "Pfmsub231" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfnmadd132 (arg0, arg1, arg2) ->
    node "Pfnmadd132" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfnmadd213 (arg0, arg1, arg2) ->
    node "Pfnmadd213" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfnmadd231 (arg0, arg1, arg2) ->
    node "Pfnmadd231" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfnmsub132 (arg0, arg1, arg2) ->
    node "Pfnmsub132" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfnmsub213 (arg0, arg1, arg2) ->
    node "Pfnmsub213" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pfnmsub231 (arg0, arg1, arg2) ->
    node "Pfnmsub231" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1; (enc_Asm_freg) arg2]
  | Asm.Pmaxsd (arg0, arg1) ->
    node "Pmaxsd" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pminsd (arg0, arg1) ->
    node "Pminsd" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pmovb_rm (arg0, arg1) ->
    node "Pmovb_rm" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovq_rf (arg0, arg1) ->
    node "Pmovq_rf" [(enc_Asm_ireg) arg0; (enc_Asm_freg) arg1]
  | Asm.Pmovsq_mr (arg0, arg1) ->
    node "Pmovsq_mr" [(enc_Asm_addrmode) arg0; (enc_Asm_freg) arg1]
  | Asm.Pmovsq_rm (arg0, arg1) ->
    node "Pmovsq_rm" [(enc_Asm_freg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pmovsb ->
    node "Pmovsb" []
  | Asm.Pmovsw ->
    node "Pmovsw" []
  | Asm.Pmovw_rm (arg0, arg1) ->
    node "Pmovw_rm" [(enc_Asm_ireg) arg0; (enc_Asm_addrmode) arg1]
  | Asm.Pnop ->
    node "Pnop" []
  | Asm.Prep_movsl ->
    node "Prep_movsl" []
  | Asm.Psbbl_rr (arg0, arg1) ->
    node "Psbbl_rr" [(enc_Asm_ireg) arg0; (enc_Asm_ireg) arg1]
  | Asm.Psqrtsd (arg0, arg1) ->
    node "Psqrtsd" [(enc_Asm_freg) arg0; (enc_Asm_freg) arg1]
  | Asm.Psubl_ri (arg0, arg1) ->
    node "Psubl_ri" [(enc_Asm_ireg) arg0; (enc_int) arg1]
  | Asm.Psubq_ri (arg0, arg1) ->
    node "Psubq_ri" [(enc_Asm_ireg) arg0; (enc_long) arg1]

and enc_Asm_coq_function (value : Asm.coq_function) =
    node "Asm_coq_function" [(enc_AST_signature) value.fn_sig; (enc_list (enc_Asm_instruction)) value.fn_code]

and enc_CFundef (value : Csyntax.coq_function Ctypes.fundef) =
  match value with
  | Ctypes.Internal (arg0) ->
    node "Internal" [(enc_Csyntax_coq_function) arg0]
  | Ctypes.External (arg0, arg1, arg2, arg3) ->
    node "External" [(enc_AST_external_function) arg0; (enc_list (enc_Ctypes_coq_type)) arg1; (enc_Ctypes_coq_type) arg2; (enc_AST_calling_convention) arg3]

and enc_CGlobvar (value : Ctypes.coq_type AST.globvar) =
    node "CGlobvar" [(enc_Ctypes_coq_type) value.gvar_info; (enc_list (enc_AST_init_data)) value.gvar_init; (enc_bool) value.gvar_readonly; (enc_bool) value.gvar_volatile]

and enc_CGlobdef (value : (Csyntax.coq_function Ctypes.fundef, Ctypes.coq_type) AST.globdef) =
  match value with
  | AST.Gfun (arg0) ->
    node "Gfun" [(enc_CFundef) arg0]
  | AST.Gvar (arg0) ->
    node "Gvar" [(enc_CGlobvar) arg0]

and enc_AFundef (value : Asm.coq_function AST.fundef) =
  match value with
  | AST.Internal (arg0) ->
    node "Internal" [(enc_Asm_coq_function) arg0]
  | AST.External (arg0) ->
    node "External" [(enc_AST_external_function) arg0]

and enc_AGlobvar (value : unit AST.globvar) =
    node "AGlobvar" [(enc_unit) value.gvar_info; (enc_list (enc_AST_init_data)) value.gvar_init; (enc_bool) value.gvar_readonly; (enc_bool) value.gvar_volatile]

and enc_AGlobdef (value : (Asm.coq_function AST.fundef, unit) AST.globdef) =
  match value with
  | AST.Gfun (arg0) ->
    node "Gfun" [(enc_AFundef) arg0]
  | AST.Gvar (arg0) ->
    node "Gvar" [(enc_AGlobvar) arg0]

and enc_AProgram (value : Asm.program) =
    node "AProgram" [(enc_list (enc_pair (enc_pos) (enc_AGlobdef))) value.prog_defs; (enc_list (enc_pos)) value.prog_public; (enc_pos) value.prog_main]

and enc_A_builtin_arg (value : Asm.preg AST.builtin_arg) =
  match value with
  | AST.BA (arg0) ->
    node "BA" [(enc_Asm_preg) arg0]
  | AST.BA_int (arg0) ->
    node "BA_int" [(enc_int) arg0]
  | AST.BA_long (arg0) ->
    node "BA_long" [(enc_long) arg0]
  | AST.BA_float (arg0) ->
    node "BA_float" [(enc_float) arg0]
  | AST.BA_single (arg0) ->
    node "BA_single" [(enc_single) arg0]
  | AST.BA_loadstack (arg0, arg1) ->
    node "BA_loadstack" [(enc_AST_memory_chunk) arg0; (enc_ptr) arg1]
  | AST.BA_addrstack (arg0) ->
    node "BA_addrstack" [(enc_ptr) arg0]
  | AST.BA_loadglobal (arg0, arg1, arg2) ->
    node "BA_loadglobal" [(enc_AST_memory_chunk) arg0; (enc_pos) arg1; (enc_ptr) arg2]
  | AST.BA_addrglobal (arg0, arg1) ->
    node "BA_addrglobal" [(enc_pos) arg0; (enc_ptr) arg1]
  | AST.BA_splitlong (arg0, arg1) ->
    node "BA_splitlong" [(enc_A_builtin_arg) arg0; (enc_A_builtin_arg) arg1]
  | AST.BA_addptr (arg0, arg1) ->
    node "BA_addptr" [(enc_A_builtin_arg) arg0; (enc_A_builtin_arg) arg1]

and enc_A_builtin_res (value : Asm.preg AST.builtin_res) =
  match value with
  | AST.BR (arg0) ->
    node "BR" [(enc_Asm_preg) arg0]
  | AST.BR_none ->
    node "BR_none" []
  | AST.BR_splitlong (arg0, arg1) ->
    node "BR_splitlong" [(enc_A_builtin_res) arg0; (enc_A_builtin_res) arg1]

let rec dec_AST_typ value : AST.typ =
  match value with
  | `List [`String "Tint"] ->
    AST.Tint
  | `List [`String "Tfloat"] ->
    AST.Tfloat
  | `List [`String "Tlong"] ->
    AST.Tlong
  | `List [`String "Tsingle"] ->
    AST.Tsingle
  | `List [`String "Tany32"] ->
    AST.Tany32
  | `List [`String "Tany64"] ->
    AST.Tany64
  | _ -> failwith "invalid AST_typ constructor or arity"

and dec_AST_xtype value : AST.xtype =
  match value with
  | `List [`String "Xbool"] ->
    AST.Xbool
  | `List [`String "Xint8signed"] ->
    AST.Xint8signed
  | `List [`String "Xint8unsigned"] ->
    AST.Xint8unsigned
  | `List [`String "Xint16signed"] ->
    AST.Xint16signed
  | `List [`String "Xint16unsigned"] ->
    AST.Xint16unsigned
  | `List [`String "Xint"] ->
    AST.Xint
  | `List [`String "Xfloat"] ->
    AST.Xfloat
  | `List [`String "Xlong"] ->
    AST.Xlong
  | `List [`String "Xsingle"] ->
    AST.Xsingle
  | `List [`String "Xptr"] ->
    AST.Xptr
  | `List [`String "Xany32"] ->
    AST.Xany32
  | `List [`String "Xany64"] ->
    AST.Xany64
  | `List [`String "Xvoid"] ->
    AST.Xvoid
  | _ -> failwith "invalid AST_xtype constructor or arity"

and dec_AST_calling_convention value : AST.calling_convention =
  match value with
  | `List [`String "AST_calling_convention"; arg0; arg1; arg2] ->
    { cc_vararg = (dec_option (dec_z)) arg0; cc_unproto = (dec_bool) arg1; cc_structret = (dec_bool) arg2 }
  | _ -> failwith "invalid AST_calling_convention constructor or arity"

and dec_AST_signature value : AST.signature =
  match value with
  | `List [`String "AST_signature"; arg0; arg1; arg2] ->
    { sig_args = (dec_list (dec_AST_xtype)) arg0; sig_res = (dec_AST_xtype) arg1; sig_cc = (dec_AST_calling_convention) arg2 }
  | _ -> failwith "invalid AST_signature constructor or arity"

and dec_AST_memory_chunk value : AST.memory_chunk =
  match value with
  | `List [`String "Mbool"] ->
    AST.Mbool
  | `List [`String "Mint8signed"] ->
    AST.Mint8signed
  | `List [`String "Mint8unsigned"] ->
    AST.Mint8unsigned
  | `List [`String "Mint16signed"] ->
    AST.Mint16signed
  | `List [`String "Mint16unsigned"] ->
    AST.Mint16unsigned
  | `List [`String "Mint32"] ->
    AST.Mint32
  | `List [`String "Mint64"] ->
    AST.Mint64
  | `List [`String "Mfloat32"] ->
    AST.Mfloat32
  | `List [`String "Mfloat64"] ->
    AST.Mfloat64
  | `List [`String "Many32"] ->
    AST.Many32
  | `List [`String "Many64"] ->
    AST.Many64
  | _ -> failwith "invalid AST_memory_chunk constructor or arity"

and dec_AST_init_data value : AST.init_data =
  match value with
  | `List [`String "Init_int8"; arg0] ->
    AST.Init_int8 ((dec_int) arg0)
  | `List [`String "Init_int16"; arg0] ->
    AST.Init_int16 ((dec_int) arg0)
  | `List [`String "Init_int32"; arg0] ->
    AST.Init_int32 ((dec_int) arg0)
  | `List [`String "Init_int64"; arg0] ->
    AST.Init_int64 ((dec_long) arg0)
  | `List [`String "Init_float32"; arg0] ->
    AST.Init_float32 ((dec_single) arg0)
  | `List [`String "Init_float64"; arg0] ->
    AST.Init_float64 ((dec_float) arg0)
  | `List [`String "Init_space"; arg0] ->
    AST.Init_space ((dec_z) arg0)
  | `List [`String "Init_addrof"; arg0; arg1] ->
    AST.Init_addrof ((dec_pos) arg0, (dec_ptr) arg1)
  | _ -> failwith "invalid AST_init_data constructor or arity"

and dec_AST_external_function value : AST.external_function =
  match value with
  | `List [`String "EF_external"; arg0; arg1] ->
    AST.EF_external ((dec_string) arg0, (dec_AST_signature) arg1)
  | `List [`String "EF_builtin"; arg0; arg1] ->
    AST.EF_builtin ((dec_string) arg0, (dec_AST_signature) arg1)
  | `List [`String "EF_runtime"; arg0; arg1] ->
    AST.EF_runtime ((dec_string) arg0, (dec_AST_signature) arg1)
  | `List [`String "EF_vload"; arg0] ->
    AST.EF_vload ((dec_AST_memory_chunk) arg0)
  | `List [`String "EF_vstore"; arg0] ->
    AST.EF_vstore ((dec_AST_memory_chunk) arg0)
  | `List [`String "EF_malloc"] ->
    AST.EF_malloc
  | `List [`String "EF_free"] ->
    AST.EF_free
  | `List [`String "EF_memcpy"; arg0; arg1] ->
    AST.EF_memcpy ((dec_z) arg0, (dec_z) arg1)
  | `List [`String "EF_annot"; arg0; arg1; arg2] ->
    AST.EF_annot ((dec_pos) arg0, (dec_string) arg1, (dec_list (dec_AST_typ)) arg2)
  | `List [`String "EF_annot_val"; arg0; arg1; arg2] ->
    AST.EF_annot_val ((dec_pos) arg0, (dec_string) arg1, (dec_AST_typ) arg2)
  | `List [`String "EF_inline_asm"; arg0; arg1; arg2] ->
    AST.EF_inline_asm ((dec_string) arg0, (dec_AST_signature) arg1, (dec_list (dec_string)) arg2)
  | `List [`String "EF_debug"; arg0; arg1; arg2] ->
    AST.EF_debug ((dec_pos) arg0, (dec_pos) arg1, (dec_list (dec_AST_typ)) arg2)
  | _ -> failwith "invalid AST_external_function constructor or arity"

and dec_Ctypes_signedness value : Ctypes.signedness =
  match value with
  | `List [`String "Signed"] ->
    Ctypes.Signed
  | `List [`String "Unsigned"] ->
    Ctypes.Unsigned
  | _ -> failwith "invalid Ctypes_signedness constructor or arity"

and dec_Ctypes_intsize value : Ctypes.intsize =
  match value with
  | `List [`String "I8"] ->
    Ctypes.I8
  | `List [`String "I16"] ->
    Ctypes.I16
  | `List [`String "I32"] ->
    Ctypes.I32
  | `List [`String "IBool"] ->
    Ctypes.IBool
  | _ -> failwith "invalid Ctypes_intsize constructor or arity"

and dec_Ctypes_floatsize value : Ctypes.floatsize =
  match value with
  | `List [`String "F32"] ->
    Ctypes.F32
  | `List [`String "F64"] ->
    Ctypes.F64
  | _ -> failwith "invalid Ctypes_floatsize constructor or arity"

and dec_Ctypes_attr value : Ctypes.attr =
  match value with
  | `List [`String "Ctypes_attr"; arg0; arg1] ->
    { attr_volatile = (dec_bool) arg0; attr_alignas = (dec_option (dec_n)) arg1 }
  | _ -> failwith "invalid Ctypes_attr constructor or arity"

and dec_Ctypes_coq_type value : Ctypes.coq_type =
  match value with
  | `List [`String "Tvoid"] ->
    Ctypes.Tvoid
  | `List [`String "Tint"; arg0; arg1; arg2] ->
    Ctypes.Tint ((dec_Ctypes_intsize) arg0, (dec_Ctypes_signedness) arg1, (dec_Ctypes_attr) arg2)
  | `List [`String "Tlong"; arg0; arg1] ->
    Ctypes.Tlong ((dec_Ctypes_signedness) arg0, (dec_Ctypes_attr) arg1)
  | `List [`String "Tfloat"; arg0; arg1] ->
    Ctypes.Tfloat ((dec_Ctypes_floatsize) arg0, (dec_Ctypes_attr) arg1)
  | `List [`String "Tpointer"; arg0; arg1] ->
    Ctypes.Tpointer ((dec_Ctypes_coq_type) arg0, (dec_Ctypes_attr) arg1)
  | `List [`String "Tarray"; arg0; arg1; arg2] ->
    Ctypes.Tarray ((dec_Ctypes_coq_type) arg0, (dec_z) arg1, (dec_Ctypes_attr) arg2)
  | `List [`String "Tfunction"; arg0; arg1; arg2] ->
    Ctypes.Tfunction ((dec_list (dec_Ctypes_coq_type)) arg0, (dec_Ctypes_coq_type) arg1, (dec_AST_calling_convention) arg2)
  | `List [`String "Tstruct"; arg0; arg1] ->
    Ctypes.Tstruct ((dec_pos) arg0, (dec_Ctypes_attr) arg1)
  | `List [`String "Tunion"; arg0; arg1] ->
    Ctypes.Tunion ((dec_pos) arg0, (dec_Ctypes_attr) arg1)
  | _ -> failwith "invalid Ctypes_coq_type constructor or arity"

and dec_Ctypes_struct_or_union value : Ctypes.struct_or_union =
  match value with
  | `List [`String "Struct"] ->
    Ctypes.Struct
  | `List [`String "Union"] ->
    Ctypes.Union
  | _ -> failwith "invalid Ctypes_struct_or_union constructor or arity"

and dec_Ctypes_member value : Ctypes.member =
  match value with
  | `List [`String "Member_plain"; arg0; arg1] ->
    Ctypes.Member_plain ((dec_pos) arg0, (dec_Ctypes_coq_type) arg1)
  | `List [`String "Member_bitfield"; arg0; arg1; arg2; arg3; arg4; arg5] ->
    Ctypes.Member_bitfield ((dec_pos) arg0, (dec_Ctypes_intsize) arg1, (dec_Ctypes_signedness) arg2, (dec_Ctypes_attr) arg3, (dec_z) arg4, (dec_bool) arg5)
  | _ -> failwith "invalid Ctypes_member constructor or arity"

and dec_Ctypes_composite_definition value : Ctypes.composite_definition =
  match value with
  | `List [`String "Composite"; arg0; arg1; arg2; arg3] ->
    Ctypes.Composite ((dec_pos) arg0, (dec_Ctypes_struct_or_union) arg1, (dec_list (dec_Ctypes_member)) arg2, (dec_Ctypes_attr) arg3)
  | _ -> failwith "invalid Ctypes_composite_definition constructor or arity"

and dec_Ctypes_bitfield value : Ctypes.bitfield =
  match value with
  | `List [`String "Full"] ->
    Ctypes.Full
  | `List [`String "Bits"; arg0; arg1; arg2; arg3] ->
    Ctypes.Bits ((dec_Ctypes_intsize) arg0, (dec_Ctypes_signedness) arg1, (dec_z) arg2, (dec_z) arg3)
  | _ -> failwith "invalid Ctypes_bitfield constructor or arity"

and dec_Cop_unary_operation value : Cop.unary_operation =
  match value with
  | `List [`String "Onotbool"] ->
    Cop.Onotbool
  | `List [`String "Onotint"] ->
    Cop.Onotint
  | `List [`String "Oneg"] ->
    Cop.Oneg
  | `List [`String "Oabsfloat"] ->
    Cop.Oabsfloat
  | _ -> failwith "invalid Cop_unary_operation constructor or arity"

and dec_Cop_binary_operation value : Cop.binary_operation =
  match value with
  | `List [`String "Oadd"] ->
    Cop.Oadd
  | `List [`String "Osub"] ->
    Cop.Osub
  | `List [`String "Omul"] ->
    Cop.Omul
  | `List [`String "Odiv"] ->
    Cop.Odiv
  | `List [`String "Omod"] ->
    Cop.Omod
  | `List [`String "Oand"] ->
    Cop.Oand
  | `List [`String "Oor"] ->
    Cop.Oor
  | `List [`String "Oxor"] ->
    Cop.Oxor
  | `List [`String "Oshl"] ->
    Cop.Oshl
  | `List [`String "Oshr"] ->
    Cop.Oshr
  | `List [`String "Oeq"] ->
    Cop.Oeq
  | `List [`String "One"] ->
    Cop.One
  | `List [`String "Olt"] ->
    Cop.Olt
  | `List [`String "Ogt"] ->
    Cop.Ogt
  | `List [`String "Ole"] ->
    Cop.Ole
  | `List [`String "Oge"] ->
    Cop.Oge
  | _ -> failwith "invalid Cop_binary_operation constructor or arity"

and dec_Cop_incr_or_decr value : Cop.incr_or_decr =
  match value with
  | `List [`String "Incr"] ->
    Cop.Incr
  | `List [`String "Decr"] ->
    Cop.Decr
  | _ -> failwith "invalid Cop_incr_or_decr constructor or arity"

and dec_Values_coq_val value : Values.coq_val =
  match value with
  | `List [`String "Vundef"] ->
    Values.Vundef
  | `List [`String "Vint"; arg0] ->
    Values.Vint ((dec_int) arg0)
  | `List [`String "Vlong"; arg0] ->
    Values.Vlong ((dec_long) arg0)
  | `List [`String "Vfloat"; arg0] ->
    Values.Vfloat ((dec_float) arg0)
  | `List [`String "Vsingle"; arg0] ->
    Values.Vsingle ((dec_single) arg0)
  | `List [`String "Vptr"; arg0; arg1] ->
    Values.Vptr ((dec_pos) arg0, (dec_ptr) arg1)
  | _ -> failwith "invalid Values_coq_val constructor or arity"

and dec_Csyntax_expr value : Csyntax.expr =
  match value with
  | `List [`String "Eval"; arg0; arg1] ->
    Csyntax.Eval ((dec_Values_coq_val) arg0, (dec_Ctypes_coq_type) arg1)
  | `List [`String "Evar"; arg0; arg1] ->
    Csyntax.Evar ((dec_pos) arg0, (dec_Ctypes_coq_type) arg1)
  | `List [`String "Efield"; arg0; arg1; arg2] ->
    Csyntax.Efield ((dec_Csyntax_expr) arg0, (dec_pos) arg1, (dec_Ctypes_coq_type) arg2)
  | `List [`String "Evalof"; arg0; arg1] ->
    Csyntax.Evalof ((dec_Csyntax_expr) arg0, (dec_Ctypes_coq_type) arg1)
  | `List [`String "Ederef"; arg0; arg1] ->
    Csyntax.Ederef ((dec_Csyntax_expr) arg0, (dec_Ctypes_coq_type) arg1)
  | `List [`String "Eaddrof"; arg0; arg1] ->
    Csyntax.Eaddrof ((dec_Csyntax_expr) arg0, (dec_Ctypes_coq_type) arg1)
  | `List [`String "Eunop"; arg0; arg1; arg2] ->
    Csyntax.Eunop ((dec_Cop_unary_operation) arg0, (dec_Csyntax_expr) arg1, (dec_Ctypes_coq_type) arg2)
  | `List [`String "Ebinop"; arg0; arg1; arg2; arg3] ->
    Csyntax.Ebinop ((dec_Cop_binary_operation) arg0, (dec_Csyntax_expr) arg1, (dec_Csyntax_expr) arg2, (dec_Ctypes_coq_type) arg3)
  | `List [`String "Ecast"; arg0; arg1] ->
    Csyntax.Ecast ((dec_Csyntax_expr) arg0, (dec_Ctypes_coq_type) arg1)
  | `List [`String "Eseqand"; arg0; arg1; arg2] ->
    Csyntax.Eseqand ((dec_Csyntax_expr) arg0, (dec_Csyntax_expr) arg1, (dec_Ctypes_coq_type) arg2)
  | `List [`String "Eseqor"; arg0; arg1; arg2] ->
    Csyntax.Eseqor ((dec_Csyntax_expr) arg0, (dec_Csyntax_expr) arg1, (dec_Ctypes_coq_type) arg2)
  | `List [`String "Econdition"; arg0; arg1; arg2; arg3] ->
    Csyntax.Econdition ((dec_Csyntax_expr) arg0, (dec_Csyntax_expr) arg1, (dec_Csyntax_expr) arg2, (dec_Ctypes_coq_type) arg3)
  | `List [`String "Esizeof"; arg0; arg1] ->
    Csyntax.Esizeof ((dec_Ctypes_coq_type) arg0, (dec_Ctypes_coq_type) arg1)
  | `List [`String "Ealignof"; arg0; arg1] ->
    Csyntax.Ealignof ((dec_Ctypes_coq_type) arg0, (dec_Ctypes_coq_type) arg1)
  | `List [`String "Eassign"; arg0; arg1; arg2] ->
    Csyntax.Eassign ((dec_Csyntax_expr) arg0, (dec_Csyntax_expr) arg1, (dec_Ctypes_coq_type) arg2)
  | `List [`String "Eassignop"; arg0; arg1; arg2; arg3; arg4] ->
    Csyntax.Eassignop ((dec_Cop_binary_operation) arg0, (dec_Csyntax_expr) arg1, (dec_Csyntax_expr) arg2, (dec_Ctypes_coq_type) arg3, (dec_Ctypes_coq_type) arg4)
  | `List [`String "Epostincr"; arg0; arg1; arg2] ->
    Csyntax.Epostincr ((dec_Cop_incr_or_decr) arg0, (dec_Csyntax_expr) arg1, (dec_Ctypes_coq_type) arg2)
  | `List [`String "Ecomma"; arg0; arg1; arg2] ->
    Csyntax.Ecomma ((dec_Csyntax_expr) arg0, (dec_Csyntax_expr) arg1, (dec_Ctypes_coq_type) arg2)
  | `List [`String "Ecall"; arg0; arg1; arg2] ->
    Csyntax.Ecall ((dec_Csyntax_expr) arg0, (dec_Csyntax_exprlist) arg1, (dec_Ctypes_coq_type) arg2)
  | `List [`String "Ebuiltin"; arg0; arg1; arg2; arg3] ->
    Csyntax.Ebuiltin ((dec_AST_external_function) arg0, (dec_list (dec_Ctypes_coq_type)) arg1, (dec_Csyntax_exprlist) arg2, (dec_Ctypes_coq_type) arg3)
  | `List [`String "Eloc"; arg0; arg1; arg2; arg3] ->
    Csyntax.Eloc ((dec_pos) arg0, (dec_ptr) arg1, (dec_Ctypes_bitfield) arg2, (dec_Ctypes_coq_type) arg3)
  | `List [`String "Eparen"; arg0; arg1; arg2] ->
    Csyntax.Eparen ((dec_Csyntax_expr) arg0, (dec_Ctypes_coq_type) arg1, (dec_Ctypes_coq_type) arg2)
  | _ -> failwith "invalid Csyntax_expr constructor or arity"

and dec_Csyntax_exprlist value : Csyntax.exprlist =
  match value with
  | `List [`String "Enil"] ->
    Csyntax.Enil
  | `List [`String "Econs"; arg0; arg1] ->
    Csyntax.Econs ((dec_Csyntax_expr) arg0, (dec_Csyntax_exprlist) arg1)
  | _ -> failwith "invalid Csyntax_exprlist constructor or arity"

and dec_Csyntax_statement value : Csyntax.statement =
  match value with
  | `List [`String "Sskip"] ->
    Csyntax.Sskip
  | `List [`String "Sdo"; arg0] ->
    Csyntax.Sdo ((dec_Csyntax_expr) arg0)
  | `List [`String "Ssequence"; arg0; arg1] ->
    Csyntax.Ssequence ((dec_Csyntax_statement) arg0, (dec_Csyntax_statement) arg1)
  | `List [`String "Sifthenelse"; arg0; arg1; arg2] ->
    Csyntax.Sifthenelse ((dec_Csyntax_expr) arg0, (dec_Csyntax_statement) arg1, (dec_Csyntax_statement) arg2)
  | `List [`String "Swhile"; arg0; arg1] ->
    Csyntax.Swhile ((dec_Csyntax_expr) arg0, (dec_Csyntax_statement) arg1)
  | `List [`String "Sdowhile"; arg0; arg1] ->
    Csyntax.Sdowhile ((dec_Csyntax_expr) arg0, (dec_Csyntax_statement) arg1)
  | `List [`String "Sfor"; arg0; arg1; arg2; arg3] ->
    Csyntax.Sfor ((dec_Csyntax_statement) arg0, (dec_Csyntax_expr) arg1, (dec_Csyntax_statement) arg2, (dec_Csyntax_statement) arg3)
  | `List [`String "Sbreak"] ->
    Csyntax.Sbreak
  | `List [`String "Scontinue"] ->
    Csyntax.Scontinue
  | `List [`String "Sreturn"; arg0] ->
    Csyntax.Sreturn ((dec_option (dec_Csyntax_expr)) arg0)
  | `List [`String "Sswitch"; arg0; arg1] ->
    Csyntax.Sswitch ((dec_Csyntax_expr) arg0, (dec_Csyntax_labeled_statements) arg1)
  | `List [`String "Slabel"; arg0; arg1] ->
    Csyntax.Slabel ((dec_pos) arg0, (dec_Csyntax_statement) arg1)
  | `List [`String "Sgoto"; arg0] ->
    Csyntax.Sgoto ((dec_pos) arg0)
  | _ -> failwith "invalid Csyntax_statement constructor or arity"

and dec_Csyntax_labeled_statements value : Csyntax.labeled_statements =
  match value with
  | `List [`String "LSnil"] ->
    Csyntax.LSnil
  | `List [`String "LScons"; arg0; arg1; arg2] ->
    Csyntax.LScons ((dec_option (dec_z)) arg0, (dec_Csyntax_statement) arg1, (dec_Csyntax_labeled_statements) arg2)
  | _ -> failwith "invalid Csyntax_labeled_statements constructor or arity"

and dec_Csyntax_coq_function value : Csyntax.coq_function =
  match value with
  | `List [`String "Csyntax_coq_function"; arg0; arg1; arg2; arg3; arg4] ->
    { fn_return = (dec_Ctypes_coq_type) arg0; fn_callconv = (dec_AST_calling_convention) arg1; fn_params = (dec_list (dec_pair (dec_pos) (dec_Ctypes_coq_type))) arg2; fn_vars = (dec_list (dec_pair (dec_pos) (dec_Ctypes_coq_type))) arg3; fn_body = (dec_Csyntax_statement) arg4 }
  | _ -> failwith "invalid Csyntax_coq_function constructor or arity"

and dec_Asm_ireg value : Asm.ireg =
  match value with
  | `List [`String "RAX"] ->
    Asm.RAX
  | `List [`String "RBX"] ->
    Asm.RBX
  | `List [`String "RCX"] ->
    Asm.RCX
  | `List [`String "RDX"] ->
    Asm.RDX
  | `List [`String "RSI"] ->
    Asm.RSI
  | `List [`String "RDI"] ->
    Asm.RDI
  | `List [`String "RBP"] ->
    Asm.RBP
  | `List [`String "RSP"] ->
    Asm.RSP
  | `List [`String "R8"] ->
    Asm.R8
  | `List [`String "R9"] ->
    Asm.R9
  | `List [`String "R10"] ->
    Asm.R10
  | `List [`String "R11"] ->
    Asm.R11
  | `List [`String "R12"] ->
    Asm.R12
  | `List [`String "R13"] ->
    Asm.R13
  | `List [`String "R14"] ->
    Asm.R14
  | `List [`String "R15"] ->
    Asm.R15
  | _ -> failwith "invalid Asm_ireg constructor or arity"

and dec_Asm_freg value : Asm.freg =
  match value with
  | `List [`String "XMM0"] ->
    Asm.XMM0
  | `List [`String "XMM1"] ->
    Asm.XMM1
  | `List [`String "XMM2"] ->
    Asm.XMM2
  | `List [`String "XMM3"] ->
    Asm.XMM3
  | `List [`String "XMM4"] ->
    Asm.XMM4
  | `List [`String "XMM5"] ->
    Asm.XMM5
  | `List [`String "XMM6"] ->
    Asm.XMM6
  | `List [`String "XMM7"] ->
    Asm.XMM7
  | `List [`String "XMM8"] ->
    Asm.XMM8
  | `List [`String "XMM9"] ->
    Asm.XMM9
  | `List [`String "XMM10"] ->
    Asm.XMM10
  | `List [`String "XMM11"] ->
    Asm.XMM11
  | `List [`String "XMM12"] ->
    Asm.XMM12
  | `List [`String "XMM13"] ->
    Asm.XMM13
  | `List [`String "XMM14"] ->
    Asm.XMM14
  | `List [`String "XMM15"] ->
    Asm.XMM15
  | _ -> failwith "invalid Asm_freg constructor or arity"

and dec_Asm_crbit value : Asm.crbit =
  match value with
  | `List [`String "ZF"] ->
    Asm.ZF
  | `List [`String "CF"] ->
    Asm.CF
  | `List [`String "PF"] ->
    Asm.PF
  | `List [`String "SF"] ->
    Asm.SF
  | `List [`String "OF"] ->
    Asm.OF
  | _ -> failwith "invalid Asm_crbit constructor or arity"

and dec_Asm_preg value : Asm.preg =
  match value with
  | `List [`String "PC"] ->
    Asm.PC
  | `List [`String "IR"; arg0] ->
    Asm.IR ((dec_Asm_ireg) arg0)
  | `List [`String "FR"; arg0] ->
    Asm.FR ((dec_Asm_freg) arg0)
  | `List [`String "ST0"] ->
    Asm.ST0
  | `List [`String "CR"; arg0] ->
    Asm.CR ((dec_Asm_crbit) arg0)
  | `List [`String "RA"] ->
    Asm.RA
  | _ -> failwith "invalid Asm_preg constructor or arity"

and dec_Asm_addrmode value : Asm.addrmode =
  match value with
  | `List [`String "Addrmode"; arg0; arg1; arg2] ->
    Asm.Addrmode ((dec_option (dec_Asm_ireg)) arg0, (dec_option (dec_pair (dec_Asm_ireg) (dec_z))) arg1, (dec_sum (dec_z) (dec_pair (dec_pos) (dec_ptr))) arg2)
  | _ -> failwith "invalid Asm_addrmode constructor or arity"

and dec_Asm_testcond value : Asm.testcond =
  match value with
  | `List [`String "Cond_e"] ->
    Asm.Cond_e
  | `List [`String "Cond_ne"] ->
    Asm.Cond_ne
  | `List [`String "Cond_b"] ->
    Asm.Cond_b
  | `List [`String "Cond_be"] ->
    Asm.Cond_be
  | `List [`String "Cond_ae"] ->
    Asm.Cond_ae
  | `List [`String "Cond_a"] ->
    Asm.Cond_a
  | `List [`String "Cond_l"] ->
    Asm.Cond_l
  | `List [`String "Cond_le"] ->
    Asm.Cond_le
  | `List [`String "Cond_ge"] ->
    Asm.Cond_ge
  | `List [`String "Cond_g"] ->
    Asm.Cond_g
  | `List [`String "Cond_p"] ->
    Asm.Cond_p
  | `List [`String "Cond_np"] ->
    Asm.Cond_np
  | _ -> failwith "invalid Asm_testcond constructor or arity"

and dec_Asm_instruction value : Asm.instruction =
  match value with
  | `List [`String "Pmov_rr"; arg0; arg1] ->
    Asm.Pmov_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovl_ri"; arg0; arg1] ->
    Asm.Pmovl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Pmovq_ri"; arg0; arg1] ->
    Asm.Pmovq_ri ((dec_Asm_ireg) arg0, (dec_long) arg1)
  | `List [`String "Pmov_rs"; arg0; arg1] ->
    Asm.Pmov_rs ((dec_Asm_ireg) arg0, (dec_pos) arg1)
  | `List [`String "Pmovl_rm"; arg0; arg1] ->
    Asm.Pmovl_rm ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovq_rm"; arg0; arg1] ->
    Asm.Pmovq_rm ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovl_mr"; arg0; arg1] ->
    Asm.Pmovl_mr ((dec_Asm_addrmode) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovq_mr"; arg0; arg1] ->
    Asm.Pmovq_mr ((dec_Asm_addrmode) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovsd_ff"; arg0; arg1] ->
    Asm.Pmovsd_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pmovsd_fi"; arg0; arg1] ->
    Asm.Pmovsd_fi ((dec_Asm_freg) arg0, (dec_float) arg1)
  | `List [`String "Pmovsd_fm"; arg0; arg1] ->
    Asm.Pmovsd_fm ((dec_Asm_freg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovsd_mf"; arg0; arg1] ->
    Asm.Pmovsd_mf ((dec_Asm_addrmode) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pmovss_fi"; arg0; arg1] ->
    Asm.Pmovss_fi ((dec_Asm_freg) arg0, (dec_single) arg1)
  | `List [`String "Pmovss_fm"; arg0; arg1] ->
    Asm.Pmovss_fm ((dec_Asm_freg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovss_mf"; arg0; arg1] ->
    Asm.Pmovss_mf ((dec_Asm_addrmode) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pfldl_m"; arg0] ->
    Asm.Pfldl_m ((dec_Asm_addrmode) arg0)
  | `List [`String "Pfstpl_m"; arg0] ->
    Asm.Pfstpl_m ((dec_Asm_addrmode) arg0)
  | `List [`String "Pflds_m"; arg0] ->
    Asm.Pflds_m ((dec_Asm_addrmode) arg0)
  | `List [`String "Pfstps_m"; arg0] ->
    Asm.Pfstps_m ((dec_Asm_addrmode) arg0)
  | `List [`String "Pmovb_mr"; arg0; arg1] ->
    Asm.Pmovb_mr ((dec_Asm_addrmode) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovw_mr"; arg0; arg1] ->
    Asm.Pmovw_mr ((dec_Asm_addrmode) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovzb_rr"; arg0; arg1] ->
    Asm.Pmovzb_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovzb_rm"; arg0; arg1] ->
    Asm.Pmovzb_rm ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovsb_rr"; arg0; arg1] ->
    Asm.Pmovsb_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovsb_rm"; arg0; arg1] ->
    Asm.Pmovsb_rm ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovzw_rr"; arg0; arg1] ->
    Asm.Pmovzw_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovzw_rm"; arg0; arg1] ->
    Asm.Pmovzw_rm ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovsw_rr"; arg0; arg1] ->
    Asm.Pmovsw_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovsw_rm"; arg0; arg1] ->
    Asm.Pmovsw_rm ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovzl_rr"; arg0; arg1] ->
    Asm.Pmovzl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovsl_rr"; arg0; arg1] ->
    Asm.Pmovsl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovls_rr"; arg0] ->
    Asm.Pmovls_rr ((dec_Asm_ireg) arg0)
  | `List [`String "Pcvtsd2ss_ff"; arg0; arg1] ->
    Asm.Pcvtsd2ss_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pcvtss2sd_ff"; arg0; arg1] ->
    Asm.Pcvtss2sd_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pcvttsd2si_rf"; arg0; arg1] ->
    Asm.Pcvttsd2si_rf ((dec_Asm_ireg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pcvtsi2sd_fr"; arg0; arg1] ->
    Asm.Pcvtsi2sd_fr ((dec_Asm_freg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pcvttss2si_rf"; arg0; arg1] ->
    Asm.Pcvttss2si_rf ((dec_Asm_ireg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pcvtsi2ss_fr"; arg0; arg1] ->
    Asm.Pcvtsi2ss_fr ((dec_Asm_freg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pcvttsd2sl_rf"; arg0; arg1] ->
    Asm.Pcvttsd2sl_rf ((dec_Asm_ireg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pcvtsl2sd_fr"; arg0; arg1] ->
    Asm.Pcvtsl2sd_fr ((dec_Asm_freg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pcvttss2sl_rf"; arg0; arg1] ->
    Asm.Pcvttss2sl_rf ((dec_Asm_ireg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pcvtsl2ss_fr"; arg0; arg1] ->
    Asm.Pcvtsl2ss_fr ((dec_Asm_freg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pleal"; arg0; arg1] ->
    Asm.Pleal ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pleaq"; arg0; arg1] ->
    Asm.Pleaq ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pnegl"; arg0] ->
    Asm.Pnegl ((dec_Asm_ireg) arg0)
  | `List [`String "Pnegq"; arg0] ->
    Asm.Pnegq ((dec_Asm_ireg) arg0)
  | `List [`String "Paddl_ri"; arg0; arg1] ->
    Asm.Paddl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Paddq_ri"; arg0; arg1] ->
    Asm.Paddq_ri ((dec_Asm_ireg) arg0, (dec_long) arg1)
  | `List [`String "Psubl_rr"; arg0; arg1] ->
    Asm.Psubl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Psubq_rr"; arg0; arg1] ->
    Asm.Psubq_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pimull_rr"; arg0; arg1] ->
    Asm.Pimull_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pimulq_rr"; arg0; arg1] ->
    Asm.Pimulq_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pimull_ri"; arg0; arg1] ->
    Asm.Pimull_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Pimulq_ri"; arg0; arg1] ->
    Asm.Pimulq_ri ((dec_Asm_ireg) arg0, (dec_long) arg1)
  | `List [`String "Pimull_r"; arg0] ->
    Asm.Pimull_r ((dec_Asm_ireg) arg0)
  | `List [`String "Pimulq_r"; arg0] ->
    Asm.Pimulq_r ((dec_Asm_ireg) arg0)
  | `List [`String "Pmull_r"; arg0] ->
    Asm.Pmull_r ((dec_Asm_ireg) arg0)
  | `List [`String "Pmulq_r"; arg0] ->
    Asm.Pmulq_r ((dec_Asm_ireg) arg0)
  | `List [`String "Pcltd"] ->
    Asm.Pcltd
  | `List [`String "Pcqto"] ->
    Asm.Pcqto
  | `List [`String "Pdivl"; arg0] ->
    Asm.Pdivl ((dec_Asm_ireg) arg0)
  | `List [`String "Pdivq"; arg0] ->
    Asm.Pdivq ((dec_Asm_ireg) arg0)
  | `List [`String "Pidivl"; arg0] ->
    Asm.Pidivl ((dec_Asm_ireg) arg0)
  | `List [`String "Pidivq"; arg0] ->
    Asm.Pidivq ((dec_Asm_ireg) arg0)
  | `List [`String "Pandl_rr"; arg0; arg1] ->
    Asm.Pandl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pandq_rr"; arg0; arg1] ->
    Asm.Pandq_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pandl_ri"; arg0; arg1] ->
    Asm.Pandl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Pandq_ri"; arg0; arg1] ->
    Asm.Pandq_ri ((dec_Asm_ireg) arg0, (dec_long) arg1)
  | `List [`String "Porl_rr"; arg0; arg1] ->
    Asm.Porl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Porq_rr"; arg0; arg1] ->
    Asm.Porq_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Porl_ri"; arg0; arg1] ->
    Asm.Porl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Porq_ri"; arg0; arg1] ->
    Asm.Porq_ri ((dec_Asm_ireg) arg0, (dec_long) arg1)
  | `List [`String "Pxorl_r"; arg0] ->
    Asm.Pxorl_r ((dec_Asm_ireg) arg0)
  | `List [`String "Pxorq_r"; arg0] ->
    Asm.Pxorq_r ((dec_Asm_ireg) arg0)
  | `List [`String "Pxorl_rr"; arg0; arg1] ->
    Asm.Pxorl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pxorq_rr"; arg0; arg1] ->
    Asm.Pxorq_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pxorl_ri"; arg0; arg1] ->
    Asm.Pxorl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Pxorq_ri"; arg0; arg1] ->
    Asm.Pxorq_ri ((dec_Asm_ireg) arg0, (dec_long) arg1)
  | `List [`String "Pnotl"; arg0] ->
    Asm.Pnotl ((dec_Asm_ireg) arg0)
  | `List [`String "Pnotq"; arg0] ->
    Asm.Pnotq ((dec_Asm_ireg) arg0)
  | `List [`String "Psall_rcl"; arg0] ->
    Asm.Psall_rcl ((dec_Asm_ireg) arg0)
  | `List [`String "Psalq_rcl"; arg0] ->
    Asm.Psalq_rcl ((dec_Asm_ireg) arg0)
  | `List [`String "Psall_ri"; arg0; arg1] ->
    Asm.Psall_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Psalq_ri"; arg0; arg1] ->
    Asm.Psalq_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Pshrl_rcl"; arg0] ->
    Asm.Pshrl_rcl ((dec_Asm_ireg) arg0)
  | `List [`String "Pshrq_rcl"; arg0] ->
    Asm.Pshrq_rcl ((dec_Asm_ireg) arg0)
  | `List [`String "Pshrl_ri"; arg0; arg1] ->
    Asm.Pshrl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Pshrq_ri"; arg0; arg1] ->
    Asm.Pshrq_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Psarl_rcl"; arg0] ->
    Asm.Psarl_rcl ((dec_Asm_ireg) arg0)
  | `List [`String "Psarq_rcl"; arg0] ->
    Asm.Psarq_rcl ((dec_Asm_ireg) arg0)
  | `List [`String "Psarl_ri"; arg0; arg1] ->
    Asm.Psarl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Psarq_ri"; arg0; arg1] ->
    Asm.Psarq_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Pshld_ri"; arg0; arg1; arg2] ->
    Asm.Pshld_ri ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1, (dec_int) arg2)
  | `List [`String "Prorl_ri"; arg0; arg1] ->
    Asm.Prorl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Prorq_ri"; arg0; arg1] ->
    Asm.Prorq_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Pcmpl_rr"; arg0; arg1] ->
    Asm.Pcmpl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pcmpq_rr"; arg0; arg1] ->
    Asm.Pcmpq_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pcmpl_ri"; arg0; arg1] ->
    Asm.Pcmpl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Pcmpq_ri"; arg0; arg1] ->
    Asm.Pcmpq_ri ((dec_Asm_ireg) arg0, (dec_long) arg1)
  | `List [`String "Ptestl_rr"; arg0; arg1] ->
    Asm.Ptestl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Ptestq_rr"; arg0; arg1] ->
    Asm.Ptestq_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Ptestl_ri"; arg0; arg1] ->
    Asm.Ptestl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Ptestq_ri"; arg0; arg1] ->
    Asm.Ptestq_ri ((dec_Asm_ireg) arg0, (dec_long) arg1)
  | `List [`String "Pcmov"; arg0; arg1; arg2] ->
    Asm.Pcmov ((dec_Asm_testcond) arg0, (dec_Asm_ireg) arg1, (dec_Asm_ireg) arg2)
  | `List [`String "Psetcc"; arg0; arg1] ->
    Asm.Psetcc ((dec_Asm_testcond) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Paddd_ff"; arg0; arg1] ->
    Asm.Paddd_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Psubd_ff"; arg0; arg1] ->
    Asm.Psubd_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pmuld_ff"; arg0; arg1] ->
    Asm.Pmuld_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pdivd_ff"; arg0; arg1] ->
    Asm.Pdivd_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pnegd"; arg0] ->
    Asm.Pnegd ((dec_Asm_freg) arg0)
  | `List [`String "Pabsd"; arg0] ->
    Asm.Pabsd ((dec_Asm_freg) arg0)
  | `List [`String "Pcomisd_ff"; arg0; arg1] ->
    Asm.Pcomisd_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pxorpd_f"; arg0] ->
    Asm.Pxorpd_f ((dec_Asm_freg) arg0)
  | `List [`String "Padds_ff"; arg0; arg1] ->
    Asm.Padds_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Psubs_ff"; arg0; arg1] ->
    Asm.Psubs_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pmuls_ff"; arg0; arg1] ->
    Asm.Pmuls_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pdivs_ff"; arg0; arg1] ->
    Asm.Pdivs_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pnegs"; arg0] ->
    Asm.Pnegs ((dec_Asm_freg) arg0)
  | `List [`String "Pabss"; arg0] ->
    Asm.Pabss ((dec_Asm_freg) arg0)
  | `List [`String "Pcomiss_ff"; arg0; arg1] ->
    Asm.Pcomiss_ff ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pxorps_f"; arg0] ->
    Asm.Pxorps_f ((dec_Asm_freg) arg0)
  | `List [`String "Pjmp_l"; arg0] ->
    Asm.Pjmp_l ((dec_pos) arg0)
  | `List [`String "Pjmp_s"; arg0; arg1] ->
    Asm.Pjmp_s ((dec_pos) arg0, (dec_AST_signature) arg1)
  | `List [`String "Pjmp_r"; arg0; arg1] ->
    Asm.Pjmp_r ((dec_Asm_ireg) arg0, (dec_AST_signature) arg1)
  | `List [`String "Pjcc"; arg0; arg1] ->
    Asm.Pjcc ((dec_Asm_testcond) arg0, (dec_pos) arg1)
  | `List [`String "Pjcc2"; arg0; arg1; arg2] ->
    Asm.Pjcc2 ((dec_Asm_testcond) arg0, (dec_Asm_testcond) arg1, (dec_pos) arg2)
  | `List [`String "Pjmptbl"; arg0; arg1] ->
    Asm.Pjmptbl ((dec_Asm_ireg) arg0, (dec_list (dec_pos)) arg1)
  | `List [`String "Pcall_s"; arg0; arg1] ->
    Asm.Pcall_s ((dec_pos) arg0, (dec_AST_signature) arg1)
  | `List [`String "Pcall_r"; arg0; arg1] ->
    Asm.Pcall_r ((dec_Asm_ireg) arg0, (dec_AST_signature) arg1)
  | `List [`String "Pret"] ->
    Asm.Pret
  | `List [`String "Pmov_rm_a"; arg0; arg1] ->
    Asm.Pmov_rm_a ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmov_mr_a"; arg0; arg1] ->
    Asm.Pmov_mr_a ((dec_Asm_addrmode) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pmovsd_fm_a"; arg0; arg1] ->
    Asm.Pmovsd_fm_a ((dec_Asm_freg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovsd_mf_a"; arg0; arg1] ->
    Asm.Pmovsd_mf_a ((dec_Asm_addrmode) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Plabel"; arg0] ->
    Asm.Plabel ((dec_pos) arg0)
  | `List [`String "Pallocframe"; arg0; arg1; arg2] ->
    Asm.Pallocframe ((dec_z) arg0, (dec_ptr) arg1, (dec_ptr) arg2)
  | `List [`String "Pfreeframe"; arg0; arg1; arg2] ->
    Asm.Pfreeframe ((dec_z) arg0, (dec_ptr) arg1, (dec_ptr) arg2)
  | `List [`String "Pbuiltin"; arg0; arg1; arg2] ->
    Asm.Pbuiltin ((dec_AST_external_function) arg0, (dec_list (dec_A_builtin_arg)) arg1, (dec_A_builtin_res) arg2)
  | `List [`String "Padcl_ri"; arg0; arg1] ->
    Asm.Padcl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Padcl_rr"; arg0; arg1] ->
    Asm.Padcl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Paddl_mi"; arg0; arg1] ->
    Asm.Paddl_mi ((dec_Asm_addrmode) arg0, (dec_int) arg1)
  | `List [`String "Paddl_rr"; arg0; arg1] ->
    Asm.Paddl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pbsfl"; arg0; arg1] ->
    Asm.Pbsfl ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pbsfq"; arg0; arg1] ->
    Asm.Pbsfq ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pbsrl"; arg0; arg1] ->
    Asm.Pbsrl ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pbsrq"; arg0; arg1] ->
    Asm.Pbsrq ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Pbswap64"; arg0] ->
    Asm.Pbswap64 ((dec_Asm_ireg) arg0)
  | `List [`String "Pbswap32"; arg0] ->
    Asm.Pbswap32 ((dec_Asm_ireg) arg0)
  | `List [`String "Pbswap16"; arg0] ->
    Asm.Pbswap16 ((dec_Asm_ireg) arg0)
  | `List [`String "Pcfi_adjust"; arg0] ->
    Asm.Pcfi_adjust ((dec_int) arg0)
  | `List [`String "Pfmadd132"; arg0; arg1; arg2] ->
    Asm.Pfmadd132 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfmadd213"; arg0; arg1; arg2] ->
    Asm.Pfmadd213 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfmadd231"; arg0; arg1; arg2] ->
    Asm.Pfmadd231 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfmsub132"; arg0; arg1; arg2] ->
    Asm.Pfmsub132 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfmsub213"; arg0; arg1; arg2] ->
    Asm.Pfmsub213 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfmsub231"; arg0; arg1; arg2] ->
    Asm.Pfmsub231 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfnmadd132"; arg0; arg1; arg2] ->
    Asm.Pfnmadd132 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfnmadd213"; arg0; arg1; arg2] ->
    Asm.Pfnmadd213 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfnmadd231"; arg0; arg1; arg2] ->
    Asm.Pfnmadd231 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfnmsub132"; arg0; arg1; arg2] ->
    Asm.Pfnmsub132 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfnmsub213"; arg0; arg1; arg2] ->
    Asm.Pfnmsub213 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pfnmsub231"; arg0; arg1; arg2] ->
    Asm.Pfnmsub231 ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1, (dec_Asm_freg) arg2)
  | `List [`String "Pmaxsd"; arg0; arg1] ->
    Asm.Pmaxsd ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pminsd"; arg0; arg1] ->
    Asm.Pminsd ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pmovb_rm"; arg0; arg1] ->
    Asm.Pmovb_rm ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovq_rf"; arg0; arg1] ->
    Asm.Pmovq_rf ((dec_Asm_ireg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pmovsq_mr"; arg0; arg1] ->
    Asm.Pmovsq_mr ((dec_Asm_addrmode) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Pmovsq_rm"; arg0; arg1] ->
    Asm.Pmovsq_rm ((dec_Asm_freg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pmovsb"] ->
    Asm.Pmovsb
  | `List [`String "Pmovsw"] ->
    Asm.Pmovsw
  | `List [`String "Pmovw_rm"; arg0; arg1] ->
    Asm.Pmovw_rm ((dec_Asm_ireg) arg0, (dec_Asm_addrmode) arg1)
  | `List [`String "Pnop"] ->
    Asm.Pnop
  | `List [`String "Prep_movsl"] ->
    Asm.Prep_movsl
  | `List [`String "Psbbl_rr"; arg0; arg1] ->
    Asm.Psbbl_rr ((dec_Asm_ireg) arg0, (dec_Asm_ireg) arg1)
  | `List [`String "Psqrtsd"; arg0; arg1] ->
    Asm.Psqrtsd ((dec_Asm_freg) arg0, (dec_Asm_freg) arg1)
  | `List [`String "Psubl_ri"; arg0; arg1] ->
    Asm.Psubl_ri ((dec_Asm_ireg) arg0, (dec_int) arg1)
  | `List [`String "Psubq_ri"; arg0; arg1] ->
    Asm.Psubq_ri ((dec_Asm_ireg) arg0, (dec_long) arg1)
  | _ -> failwith "invalid Asm_instruction constructor or arity"

and dec_Asm_coq_function value : Asm.coq_function =
  match value with
  | `List [`String "Asm_coq_function"; arg0; arg1] ->
    { fn_sig = (dec_AST_signature) arg0; fn_code = (dec_list (dec_Asm_instruction)) arg1 }
  | _ -> failwith "invalid Asm_coq_function constructor or arity"

and dec_CFundef value : Csyntax.coq_function Ctypes.fundef =
  match value with
  | `List [`String "Internal"; arg0] ->
    Ctypes.Internal ((dec_Csyntax_coq_function) arg0)
  | `List [`String "External"; arg0; arg1; arg2; arg3] ->
    Ctypes.External ((dec_AST_external_function) arg0, (dec_list (dec_Ctypes_coq_type)) arg1, (dec_Ctypes_coq_type) arg2, (dec_AST_calling_convention) arg3)
  | _ -> failwith "invalid CFundef constructor or arity"

and dec_CGlobvar value : Ctypes.coq_type AST.globvar =
  match value with
  | `List [`String "CGlobvar"; arg0; arg1; arg2; arg3] ->
    { gvar_info = (dec_Ctypes_coq_type) arg0; gvar_init = (dec_list (dec_AST_init_data)) arg1; gvar_readonly = (dec_bool) arg2; gvar_volatile = (dec_bool) arg3 }
  | _ -> failwith "invalid CGlobvar constructor or arity"

and dec_CGlobdef value : (Csyntax.coq_function Ctypes.fundef, Ctypes.coq_type) AST.globdef =
  match value with
  | `List [`String "Gfun"; arg0] ->
    AST.Gfun ((dec_CFundef) arg0)
  | `List [`String "Gvar"; arg0] ->
    AST.Gvar ((dec_CGlobvar) arg0)
  | _ -> failwith "invalid CGlobdef constructor or arity"

and dec_AFundef value : Asm.coq_function AST.fundef =
  match value with
  | `List [`String "Internal"; arg0] ->
    AST.Internal ((dec_Asm_coq_function) arg0)
  | `List [`String "External"; arg0] ->
    AST.External ((dec_AST_external_function) arg0)
  | _ -> failwith "invalid AFundef constructor or arity"

and dec_AGlobvar value : unit AST.globvar =
  match value with
  | `List [`String "AGlobvar"; arg0; arg1; arg2; arg3] ->
    { gvar_info = (dec_unit) arg0; gvar_init = (dec_list (dec_AST_init_data)) arg1; gvar_readonly = (dec_bool) arg2; gvar_volatile = (dec_bool) arg3 }
  | _ -> failwith "invalid AGlobvar constructor or arity"

and dec_AGlobdef value : (Asm.coq_function AST.fundef, unit) AST.globdef =
  match value with
  | `List [`String "Gfun"; arg0] ->
    AST.Gfun ((dec_AFundef) arg0)
  | `List [`String "Gvar"; arg0] ->
    AST.Gvar ((dec_AGlobvar) arg0)
  | _ -> failwith "invalid AGlobdef constructor or arity"

and dec_AProgram value : Asm.program =
  match value with
  | `List [`String "AProgram"; arg0; arg1; arg2] ->
    { prog_defs = (dec_list (dec_pair (dec_pos) (dec_AGlobdef))) arg0; prog_public = (dec_list (dec_pos)) arg1; prog_main = (dec_pos) arg2 }
  | _ -> failwith "invalid AProgram constructor or arity"

and dec_A_builtin_arg value : Asm.preg AST.builtin_arg =
  match value with
  | `List [`String "BA"; arg0] ->
    AST.BA ((dec_Asm_preg) arg0)
  | `List [`String "BA_int"; arg0] ->
    AST.BA_int ((dec_int) arg0)
  | `List [`String "BA_long"; arg0] ->
    AST.BA_long ((dec_long) arg0)
  | `List [`String "BA_float"; arg0] ->
    AST.BA_float ((dec_float) arg0)
  | `List [`String "BA_single"; arg0] ->
    AST.BA_single ((dec_single) arg0)
  | `List [`String "BA_loadstack"; arg0; arg1] ->
    AST.BA_loadstack ((dec_AST_memory_chunk) arg0, (dec_ptr) arg1)
  | `List [`String "BA_addrstack"; arg0] ->
    AST.BA_addrstack ((dec_ptr) arg0)
  | `List [`String "BA_loadglobal"; arg0; arg1; arg2] ->
    AST.BA_loadglobal ((dec_AST_memory_chunk) arg0, (dec_pos) arg1, (dec_ptr) arg2)
  | `List [`String "BA_addrglobal"; arg0; arg1] ->
    AST.BA_addrglobal ((dec_pos) arg0, (dec_ptr) arg1)
  | `List [`String "BA_splitlong"; arg0; arg1] ->
    AST.BA_splitlong ((dec_A_builtin_arg) arg0, (dec_A_builtin_arg) arg1)
  | `List [`String "BA_addptr"; arg0; arg1] ->
    AST.BA_addptr ((dec_A_builtin_arg) arg0, (dec_A_builtin_arg) arg1)
  | _ -> failwith "invalid A_builtin_arg constructor or arity"

and dec_A_builtin_res value : Asm.preg AST.builtin_res =
  match value with
  | `List [`String "BR"; arg0] ->
    AST.BR ((dec_Asm_preg) arg0)
  | `List [`String "BR_none"] ->
    AST.BR_none
  | `List [`String "BR_splitlong"; arg0; arg1] ->
    AST.BR_splitlong ((dec_A_builtin_res) arg0, (dec_A_builtin_res) arg1)
  | _ -> failwith "invalid A_builtin_res constructor or arity"
