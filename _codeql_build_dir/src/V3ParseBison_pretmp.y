// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Bison grammar file
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// Original code here by Paul Wasson and Duane Galbi
//*************************************************************************
// clang-format off

%{
#ifdef NEVER_JUST_FOR_CLANG_FORMAT
 }
#endif
// clang-format on
#include "V3ParseGrammar.h"  // Defines YYTYPE; before including bison header

#define YYERROR_VERBOSE 1  // For prior to Bison 3.6
#define YYINITDEPTH 10000  // Older bisons ignore YYMAXDEPTH
#define YYMAXDEPTH 10000

// Pick up new lexer
#define yylex PARSEP->tokenToBison

#define BBCOVERIGN(fl, msg) (fl)->v3warn(COVERIGN, msg)
#define BBUNSUP(fl, msg) (fl)->v3warn(E_UNSUPPORTED, msg)
#define GATEUNSUP(fl, tok) \
    { BBUNSUP((fl), "Unsupported: Verilog 1995 gate primitive: " << (tok)); }
#define RISEFALLDLYUNSUP(nodep) \
    if (nodep->fileline()->timingOn() && v3Global.opt.timing().isSetTrue()) { \
        nodep->v3warn(RISEFALLDLY, \
                      "Unsupported: rising/falling/turn-off delays. Using the first delay"); \
    }
#define MINTYPMAXDLYUNSUP(nodep) \
    if (nodep->fileline()->timingOn() && v3Global.opt.timing().isSetTrue()) { \
        nodep->v3warn( \
            MINTYPMAXDLY, \
            "Unsupported: minimum/typical/maximum delay expressions. Using the typical delay"); \
    }
// Apply a delay to all continuous assignments under listp
static void DELAY_LIST(AstNode* listp, AstDelay* delayp) {
    if (!delayp) return;
    for (AstNode* nodep = listp; nodep; nodep = nodep->nextp()) {
        if (VN_IS(nodep, Implicit)) continue;
        AstAlways* const alwaysp = VN_AS(nodep, Always);
        AstAssignW* const assignp = VN_AS(alwaysp->stmtsp(), AssignW);
        assignp->timingControlp(delayp->backp() ? delayp->cloneTree(false) : delayp);
    }
}
// Apply a strength to all continuous assignments under listp
static void STRENGTH_LIST(AstNode* listp, AstStrengthSpec* specp) {
    if (!specp) return;
    for (AstNode* nodep = listp; nodep; nodep = nodep->nextp()) {
        if (VN_IS(nodep, Implicit)) continue;
        AstAlways* const alwaysp = VN_AS(nodep, Always);
        AstAssignW* const assignp = VN_AS(alwaysp->stmtsp(), AssignW);
        assignp->strengthSpecp(specp->backp() ? specp->cloneTree(false) : specp);
    }
}
static void STRENGTHUNSUP(AstStrengthSpec* nodep) {
    if (!nodep) return;
    BBUNSUP((nodep->fileline()), "Unsupported: Strength specifier on this gate type");
    nodep->deleteTree();
}

//======================================================================
// Statics (for here only)

#define PARSEP V3ParseImp::parsep()
#define GRAMMARP V3ParseGrammar::singletonp()

const VBasicDTypeKwd LOGIC = VBasicDTypeKwd::LOGIC;  // Shorthand "LOGIC"
const VBasicDTypeKwd LOGIC_IMPLICIT = VBasicDTypeKwd::LOGIC_IMPLICIT;

//======================================================================
// Macro functions

// Only use in empty rules, so lines point at beginnings
#define CRELINE() (PARSEP->bisonLastFileline()->copyOrSameFileLineApplied())
#define FILELINE_OR_CRE(nodep) ((nodep) ? (nodep)->fileline() : CRELINE())

#define VARRESET_LIST(decl) VARRESET__PVT(decl, 1)  // Start of pinlist
#define VARRESET_NONLIST(decl) VARRESET__PVT(decl, 0);  // Not in a pinlist
#define VARRESET__PVT(decl, pinNumStart) \
    { \
        VARDECL(decl); \
        VARIO(NONE); \
        VARDTYPE_NDECL(nullptr); \
        GRAMMARP->m_pinNum = (pinNumStart); \
        GRAMMARP->m_varLifetime = VLifetime::NONE; \
        GRAMMARP->m_varDeclTyped = false; \
    }
#define VARDECL(type) \
    { GRAMMARP->m_varDecl = VVarType::type; }
#define VARIO(type) \
    { GRAMMARP->m_varIO = VDirection::type; }
// Set direction to default-input when detect inside an ANSI port list
#define VARIOANSI() \
    { \
        if (GRAMMARP->m_varIO == VDirection::NONE) VARIO(INPUT); \
    }
#define VARLIFE(flag) \
    { GRAMMARP->m_varLifetime = flag; }
#define VARDTYPE(dtypep) \
    { \
        GRAMMARP->setDType(dtypep); \
        GRAMMARP->m_varDeclTyped = true; \
    }
#define VARDTYPE_NDECL(dtypep) \
    { GRAMMARP->setDType(dtypep); }  // Port that is range or signed only (not a decl)

#define VARDONEA(fl, name, array, attrs) GRAMMARP->createVariable((fl), (name), (array), (attrs))
#define VARDONEP(portp, array, attrs) \
    GRAMMARP->createVariable((portp)->fileline(), (portp)->name(), (array), (attrs))
#define PINNUMINC() (GRAMMARP->m_pinNum++)

#define GATERANGE(rangep) \
    { GRAMMARP->m_gateRangep = rangep; }

#define INSTPREP(modfl, modname, paramsp) \
    { \
        GRAMMARP->m_impliedDecl = true; \
        GRAMMARP->m_instModuleFl = modfl; \
        GRAMMARP->m_instModule = modname; \
        GRAMMARP->m_instParamp = paramsp; \
    }

#define DEL(...) \
    { \
        AstNode* const nodeps[] = {__VA_ARGS__}; \
        for (AstNode* const nodep : nodeps) \
            if (nodep) nodep->deleteTree(); \
    }

static void ERRSVKWD(FileLine* fileline, const string& tokname) {
    static int s_toldonce = 0;
    fileline->v3error(
        "Unexpected '"s + tokname + "': '" + tokname
        + "' is a SystemVerilog keyword misused as an identifier."
        + (!s_toldonce++ ? "\n" + fileline->warnMore()
                               + "... Suggest modify the Verilog-2001 code to avoid SV keywords,"
                               + " or use `begin_keywords or --language."
                         : ""));
}

static void ASSIGNEQEXPR(FileLine* fileline) {
    fileline->v3warn(ASSIGNEQEXPR,
                     "Assignment '=' inside expression\n"
                         << fileline->warnMore()
                         << "... Was a '==' intended, or suggest use a separate statement");
}

static void UNSUPREAL(FileLine* fileline) {
    fileline->v3warn(SHORTREAL,
                     "Unsupported: shortreal being promoted to real (suggest use real instead)");
}

//======================================================================

void yyerror(const char* errmsg) { PARSEP->bisonLastFileline()->v3error(errmsg); }

template <typename T_Node, typename T_Next>
static T_Node* addNextNull(T_Node* nodep, T_Next* nextp) {
    if (!nextp) return nodep;
    return AstNode::addNext<T_Node, T_Next>(nodep, nextp);
}

//======================================================================

class AstSenTree;
// clang-format off
%}

// Bison 3.0 and newer
%define parse.error verbose

// We run bison with the -d argument. This tells it to generate a
// header file with token names. Old versions of bison pasted the
// contents of that file into the generated source as well; newer
// versions just include it.
//
// Since we run bison through ../bisonpre, it doesn't know the correct
// header file name, so we need to tell it.
%define api.header.include {"V3ParseBison.h"}

// When writing Bison patterns we use yTOKEN instead of "token",
// so Bison will error out on unknown "token"s.

// Generic lexer tokens, for example a number
// IEEE: real_number
%token<cdouble>         yaFLOATNUM      "FLOATING-POINT NUMBER"

// IEEE: identifier, class_identifier, class_variable_identifier,
// covergroup_variable_identifier, dynamic_array_variable_identifier,
// enum_identifier, interface_identifier, interface_instance_identifier,
// package_identifier, type_identifier, variable_identifier,
%token<strp>            yaID__ETC       "IDENTIFIER"
%token<strp>            yaID__CC        "IDENTIFIER-::"
%token<strp>            yaID__LEX       "IDENTIFIER-in-lex"
%token<strp>            yaID__PATHPULSE "IDENTIFIER-for-pathpulse"
%token<strp>            yaID__aINST     "IDENTIFIER-for-instance"
%token<strp>            yaID__aTYPE     "IDENTIFIER-for-type"
//                      Can't predecode aFUNCTION, can declare after use
//                      Can't predecode aINTERFACE, can declare after use
//                      Can't predecode aTASK, can declare after use

// IEEE: integral_number
%token<nump>            yaINTNUM        "INTEGER NUMBER"
// IEEE: time_literal + time_unit
%token<cdouble>         yaTIMENUM       "TIME NUMBER"
// IEEE: string_literal
%token<strp>            yaSTRING        "STRING"
%token<strp>            yaSTRING__IGNORE "STRING-ignored"       // Used when expr:string not allowed
// IEEE: edge_descriptor
%token<nump>            yaEDGEDESC      "EDGE DESCRIPTOR"

%token<fl>              yaTIMINGSPEC    "TIMING SPEC ELEMENT"

%token<fl>              ygenSTRENGTH    "STRENGTH keyword (strong1/etc)"

%token<strp>            yaTABLE_FIELD   "UDP table field"
%token<fl>              yaTABLE_LRSEP   ":"
%token<fl>              yaTABLE_LINEEND "UDP table line end"

%token<strp>            yaSCCTOR        "`systemc_ctor block"
%token<strp>            yaSCDTOR        "`systemc_dtor block"
%token<strp>            yaSCHDR         "`systemc_header block"
%token<strp>            yaSCHDRP        "`systemc_header_post block"
%token<strp>            yaSCIMP         "`systemc_implementation block"
%token<strp>            yaSCIMPH        "`systemc_imp_header block"
%token<strp>            yaSCINT         "`systemc_interface block"

%token<fl>              yVLT_CLOCKER                "clocker"
%token<fl>              yVLT_CLOCK_ENABLE           "clock_enable"
%token<fl>              yVLT_COVERAGE_BLOCK_OFF     "coverage_block_off"
%token<fl>              yVLT_COVERAGE_OFF           "coverage_off"
%token<fl>              yVLT_COVERAGE_ON            "coverage_on"
%token<fl>              yVLT_FORCEABLE              "forceable"
%token<fl>              yVLT_FULL_CASE              "full_case"
%token<fl>              yVLT_HIER_BLOCK             "hier_block"
%token<fl>              yVLT_HIER_PARAMS            "hier_params"
%token<fl>              yVLT_HIER_WORKERS           "hier_workers"
%token<fl>              yVLT_INLINE                 "inline"
%token<fl>              yVLT_ISOLATE_ASSIGNMENTS    "isolate_assignments"
%token<fl>              yVLT_LINT_OFF               "lint_off"
%token<fl>              yVLT_LINT_ON                "lint_on"
%token<fl>              yVLT_NO_CLOCKER             "no_clocker"
%token<fl>              yVLT_NO_INLINE              "no_inline"
%token<fl>              yVLT_PARALLEL_CASE          "parallel_case"
%token<fl>              yVLT_PROFILE_DATA           "profile_data"
%token<fl>              yVLT_PUBLIC                 "public"
%token<fl>              yVLT_PUBLIC_FLAT            "public_flat"
%token<fl>              yVLT_PUBLIC_FLAT_RD         "public_flat_rd"
%token<fl>              yVLT_PUBLIC_FLAT_RW         "public_flat_rw"
%token<fl>              yVLT_PUBLIC_MODULE          "public_module"
%token<fl>              yVLT_SC_BIGUINT             "sc_biguint"
%token<fl>              yVLT_SC_BV                  "sc_bv"
%token<fl>              yVLT_SFORMAT                "sformat"
%token<fl>              yVLT_SPLIT_VAR              "split_var"
%token<fl>              yVLT_TIMING_OFF             "timing_off"
%token<fl>              yVLT_TIMING_ON              "timing_on"
%token<fl>              yVLT_TRACING_OFF            "tracing_off"
%token<fl>              yVLT_TRACING_ON             "tracing_on"

%token<fl>              yVLT_D_BLOCK    "--block"
%token<fl>              yVLT_D_CONTENTS "--contents"
%token<fl>              yVLT_D_COST     "--cost"
%token<fl>              yVLT_D_FILE     "--file"
%token<fl>              yVLT_D_FUNCTION "--function"
%token<fl>              yVLT_D_HIER_DPI "--hier-dpi"
%token<fl>              yVLT_D_LEVELS   "--levels"
%token<fl>              yVLT_D_LINES    "--lines"
%token<fl>              yVLT_D_MATCH    "--match"
%token<fl>              yVLT_D_MODEL    "--model"
%token<fl>              yVLT_D_MODULE   "--module"
%token<fl>              yVLT_D_MTASK    "--mtask"
%token<fl>              yVLT_D_PARAM    "--param"
%token<fl>              yVLT_D_PORT     "--port"
%token<fl>              yVLT_D_RULE     "--rule"
%token<fl>              yVLT_D_SCOPE    "--scope"
%token<fl>              yVLT_D_TASK     "--task"
%token<fl>              yVLT_D_VAR      "--var"
%token<fl>              yVLT_D_WORKERS  "--workers"

%token<strp>            yaD_PLI         "${pli-system}"

%token<fl>              yaT_NOUNCONNECTED  "`nounconnecteddrive"
%token<fl>              yaT_RESETALL    "`resetall"
%token<fl>              yaT_UNCONNECTED_PULL0  "`unconnected_drive pull0"
%token<fl>              yaT_UNCONNECTED_PULL1  "`unconnected_drive pull1"

// <fl> is the fileline, abbreviated to shorten "$<fl>1" references
%token<fl>              '!'
%token<fl>              '#'
%token<fl>              '%'
%token<fl>              '&'
%token<fl>              '('  // See also yP_PAR__STRENGTH
%token<fl>              ')'
%token<fl>              '*'
%token<fl>              '+'
%token<fl>              ','
%token<fl>              '-'
%token<fl>              '.'
%token<fl>              '/'
%token<fl>              ':'  // See also yP_COLON__BEGIN or yP_COLON__FORK
%token<fl>              ';'
%token<fl>              '<'
%token<fl>              '='  // See also yP_EQ__NEW
%token<fl>              '>'
%token<fl>              '?'
%token<fl>              '@'
%token<fl>              '['
%token<fl>              ']'
%token<fl>              '^'
%token<fl>              '{'
%token<fl>              '|'
%token<fl>              '}'
%token<fl>              '~'

// Specific keywords
// yKEYWORD means match "keyword"
// Other cases are yXX_KEYWORD where XX makes it unique,
// for example yP_ for punctuation based operators.
// Double underscores "yX__Y" means token X followed by Y,
// and "yX__ETC" means X folled by everything but Y(s).
%token<fl>              y1STEP          "1step"
%token<fl>              yACCEPT_ON      "accept_on"
%token<fl>              yALIAS          "alias"
%token<fl>              yALWAYS         "always"
%token<fl>              yALWAYS_COMB    "always_comb"
%token<fl>              yALWAYS_FF      "always_ff"
%token<fl>              yALWAYS_LATCH   "always_latch"
%token<fl>              yAND            "and"
%token<fl>              yASSERT         "assert"
%token<fl>              yASSIGN         "assign"
%token<fl>              yASSUME         "assume"
%token<fl>              yAUTOMATIC      "automatic"
%token<fl>              yBEFORE         "before"
%token<fl>              yBEGIN          "begin"
%token<fl>              yBIND           "bind"
%token<fl>              yBINS           "bins"
%token<fl>              yBINSOF         "binsof"
%token<fl>              yBIT            "bit"
%token<fl>              yBREAK          "break"
%token<fl>              yBUF            "buf"
%token<fl>              yBUFIF0         "bufif0"
%token<fl>              yBUFIF1         "bufif1"
%token<fl>              yBYTE           "byte"
%token<fl>              yCASE           "case"
%token<fl>              yCASEX          "casex"
%token<fl>              yCASEZ          "casez"
%token<fl>              yCELL           "cell"
%token<fl>              yCHANDLE        "chandle"
%token<fl>              yCHECKER        "checker"
%token<fl>              yCLASS          "class"
%token<fl>              yCLOCKING       "clocking"
%token<fl>              yCMOS           "cmos"
%token<fl>              yCONFIG         "config"
%token<fl>              yCONSTRAINT     "constraint"
%token<fl>              yCONST__ETC     "const"
%token<fl>              yCONST__LEX     "const-in-lex"
%token<fl>              yCONST__REF     "const-then-ref"
%token<fl>              yCONTEXT        "context"
%token<fl>              yCONTINUE       "continue"
%token<fl>              yCOVER          "cover"
%token<fl>              yCOVERGROUP     "covergroup"
%token<fl>              yCOVERPOINT     "coverpoint"
%token<fl>              yCROSS          "cross"
%token<fl>              yDEASSIGN       "deassign"
%token<fl>              yDEFAULT        "default"
%token<fl>              yDEFPARAM       "defparam"
%token<fl>              yDESIGN         "design"
%token<fl>              yDISABLE        "disable"
%token<fl>              yDIST           "dist"
%token<fl>              yDO             "do"
%token<fl>              yEDGE           "edge"
%token<fl>              yELSE           "else"
%token<fl>              yEND            "end"
%token<fl>              yENDCASE        "endcase"
%token<fl>              yENDCHECKER     "endchecker"
%token<fl>              yENDCLASS       "endclass"
%token<fl>              yENDCLOCKING    "endclocking"
%token<fl>              yENDCONFIG      "endconfig"
%token<fl>              yENDFUNCTION    "endfunction"
%token<fl>              yENDGENERATE    "endgenerate"
%token<fl>              yENDGROUP       "endgroup"
%token<fl>              yENDINTERFACE   "endinterface"
%token<fl>              yENDMODULE      "endmodule"
%token<fl>              yENDPACKAGE     "endpackage"
%token<fl>              yENDPRIMITIVE   "endprimitive"
%token<fl>              yENDPROGRAM     "endprogram"
%token<fl>              yENDPROPERTY    "endproperty"
%token<fl>              yENDSEQUENCE    "endsequence"
%token<fl>              yENDSPECIFY     "endspecify"
%token<fl>              yENDTABLE       "endtable"
%token<fl>              yENDTASK        "endtask"
%token<fl>              yENUM           "enum"
%token<fl>              yEVENT          "event"
%token<fl>              yEVENTUALLY     "eventually"
%token<fl>              yEXPECT         "expect"
%token<fl>              yEXPORT         "export"
%token<fl>              yEXTENDS        "extends"
%token<fl>              yEXTERN         "extern"
%token<fl>              yFINAL          "final"
%token<fl>              yFIRST_MATCH    "first_match"
%token<fl>              yFOR            "for"
%token<fl>              yFORCE          "force"
%token<fl>              yFOREACH        "foreach"
%token<fl>              yFOREVER        "forever"
%token<fl>              yFORK           "fork"
%token<fl>              yFORKJOIN       "forkjoin"
%token<fl>              yFUNCTION       "function"
%token<fl>              yGENERATE       "generate"
%token<fl>              yGENVAR         "genvar"
%token<fl>              yGLOBAL__CLOCKING "global-then-clocking"
%token<fl>              yGLOBAL__ETC    "global"
%token<fl>              yGLOBAL__LEX    "global-in-lex"
%token<fl>              yHIGHZ0         "highz0"
%token<fl>              yHIGHZ1         "highz1"
%token<fl>              yIF             "if"
%token<fl>              yIFF            "iff"
%token<fl>              yIGNORE_BINS    "ignore_bins"
%token<fl>              yILLEGAL_BINS   "illegal_bins"
%token<fl>              yIMPLEMENTS     "implements"
%token<fl>              yIMPLIES        "implies"
%token<fl>              yIMPORT         "import"
%token<fl>              yINCDIR         "incdir"
%token<fl>              yINCLUDE        "include"
%token<fl>              yINITIAL        "initial"
%token<fl>              yINOUT          "inout"
%token<fl>              yINPUT          "input"
%token<fl>              yINSIDE         "inside"
%token<fl>              yINSTANCE       "instance"
%token<fl>              yINT            "int"
%token<fl>              yINTEGER        "integer"
%token<fl>              yINTERCONNECT   "interconnect"
%token<fl>              yINTERFACE      "interface"
%token<fl>              yINTERSECT      "intersect"
%token<fl>              yJOIN           "join"
%token<fl>              yJOIN_ANY       "join_any"
%token<fl>              yJOIN_NONE      "join_none"
%token<fl>              yLET            "let"
%token<fl>              yLIBLIST        "liblist"
%token<fl>              yLIBRARY        "library"
%token<fl>              yLOCALPARAM     "localparam"
%token<fl>              yLOCAL__COLONCOLON "local-then-::"
%token<fl>              yLOCAL__ETC     "local"
%token<fl>              yLOCAL__LEX     "local-in-lex"
%token<fl>              yLOGIC          "logic"
%token<fl>              yLONGINT        "longint"
%token<fl>              yMATCHES        "matches"
%token<fl>              yMODPORT        "modport"
%token<fl>              yMODULE         "module"
%token<fl>              yNAND           "nand"
%token<fl>              yNEGEDGE        "negedge"
%token<fl>              yNETTYPE        "nettype"
%token<fl>              yNEW__ETC       "new"
%token<fl>              yNEW__LEX       "new-in-lex"
%token<fl>              yNEW__PAREN     "new-then-paren"
%token<fl>              yNEXTTIME       "nexttime"
%token<fl>              yNMOS           "nmos"
%token<fl>              yNOR            "nor"
%token<fl>              yNOT            "not"
%token<fl>              yNOTIF0         "notif0"
%token<fl>              yNOTIF1         "notif1"
%token<fl>              yNULL           "null"
%token<fl>              yOR             "or"
%token<fl>              yOUTPUT         "output"
%token<fl>              yPACKAGE        "package"
%token<fl>              yPACKED         "packed"
%token<fl>              yPARAMETER      "parameter"
%token<fl>              yPMOS           "pmos"
%token<fl>              yPOSEDGE        "posedge"
%token<fl>              yPRIMITIVE      "primitive"
%token<fl>              yPRIORITY       "priority"
%token<fl>              yPROGRAM        "program"
%token<fl>              yPROPERTY       "property"
%token<fl>              yPROTECTED      "protected"
%token<fl>              yPULL0          "pull0"
%token<fl>              yPULL1          "pull1"
%token<fl>              yPULLDOWN       "pulldown"
%token<fl>              yPULLUP         "pullup"
%token<fl>              yPURE           "pure"
%token<fl>              yRAND           "rand"
%token<fl>              yRANDC          "randc"
%token<fl>              yRANDCASE       "randcase"
%token<fl>              yRANDOMIZE      "randomize"
%token<fl>              yRANDSEQUENCE   "randsequence"
%token<fl>              yRCMOS          "rcmos"
%token<fl>              yREAL           "real"
%token<fl>              yREALTIME       "realtime"
%token<fl>              yREF            "ref"
%token<fl>              yREG            "reg"
%token<fl>              yREJECT_ON      "reject_on"
%token<fl>              yRELEASE        "release"
%token<fl>              yREPEAT         "repeat"
%token<fl>              yRESTRICT       "restrict"
%token<fl>              yRETURN         "return"
%token<fl>              yRNMOS          "rnmos"
%token<fl>              yRPMOS          "rpmos"
%token<fl>              yRTRAN          "rtran"
%token<fl>              yRTRANIF0       "rtranif0"
%token<fl>              yRTRANIF1       "rtranif1"
%token<fl>              ySCALARED       "scalared"
%token<fl>              ySEQUENCE       "sequence"
%token<fl>              ySHORTINT       "shortint"
%token<fl>              ySHORTREAL      "shortreal"
%token<fl>              ySIGNED         "signed"
%token<fl>              ySOFT           "soft"
%token<fl>              ySOLVE          "solve"
%token<fl>              ySPECIFY        "specify"
%token<fl>              ySPECPARAM      "specparam"
%token<fl>              ySTATIC__CONSTRAINT "static-then-constraint"
%token<fl>              ySTATIC__ETC    "static"
%token<fl>              ySTATIC__LEX    "static-in-lex"
%token<fl>              ySTRING         "string"
%token<fl>              ySTRONG         "strong"
%token<fl>              ySTRONG0        "strong0"
%token<fl>              ySTRONG1        "strong1"
%token<fl>              ySTRUCT         "struct"
%token<fl>              ySUPER          "super"
%token<fl>              ySUPPLY0        "supply0"
%token<fl>              ySUPPLY1        "supply1"
%token<fl>              ySYNC_ACCEPT_ON "sync_accept_on"
%token<fl>              ySYNC_REJECT_ON "sync_reject_on"
%token<fl>              yS_ALWAYS       "s_always"
%token<fl>              yS_EVENTUALLY   "s_eventually"
%token<fl>              yS_NEXTTIME     "s_nexttime"
%token<fl>              yS_UNTIL        "s_until"
%token<fl>              yS_UNTIL_WITH   "s_until_with"
%token<fl>              yTABLE          "table"
%token<fl>              yTAGGED         "tagged"
%token<fl>              yTASK           "task"
%token<fl>              yTHIS           "this"
%token<fl>              yTHROUGHOUT     "throughout"
%token<fl>              yTIME           "time"
%token<fl>              yTIMEPRECISION  "timeprecision"
%token<fl>              yTIMEUNIT       "timeunit"
%token<fl>              yTRAN           "tran"
%token<fl>              yTRANIF0        "tranif0"
%token<fl>              yTRANIF1        "tranif1"
%token<fl>              yTRI            "tri"
%token<fl>              yTRI0           "tri0"
%token<fl>              yTRI1           "tri1"
%token<fl>              yTRIAND         "triand"
%token<fl>              yTRIOR          "trior"
%token<fl>              yTRIREG         "trireg"
%token<fl>              yTRUE           "true"
%token<fl>              yTYPEDEF        "typedef"
%token<fl>              yTYPE__EQ       "type-then-eqneq"
%token<fl>              yTYPE__ETC      "type"
%token<fl>              yTYPE__LEX      "type-in-lex"
%token<fl>              yUNION          "union"
%token<fl>              yUNIQUE         "unique"
%token<fl>              yUNIQUE0        "unique0"
%token<fl>              yUNSIGNED       "unsigned"
%token<fl>              yUNTIL          "until"
%token<fl>              yUNTIL_WITH     "until_with"
%token<fl>              yUNTYPED        "untyped"
%token<fl>              yUSE            "use"
%token<fl>              yVAR            "var"
%token<fl>              yVECTORED       "vectored"
%token<fl>              yVIRTUAL__CLASS "virtual-then-class"
%token<fl>              yVIRTUAL__ETC   "virtual"
%token<fl>              yVIRTUAL__INTERFACE     "virtual-then-interface"
%token<fl>              yVIRTUAL__LEX   "virtual-in-lex"
%token<fl>              yVIRTUAL__anyID "virtual-then-identifier"
%token<fl>              yVOID           "void"
%token<fl>              yWAIT           "wait"
%token<fl>              yWAIT_ORDER     "wait_order"
%token<fl>              yWAND           "wand"
%token<fl>              yWEAK           "weak"
%token<fl>              yWEAK0          "weak0"
%token<fl>              yWEAK1          "weak1"
%token<fl>              yWHILE          "while"
%token<fl>              yWILDCARD       "wildcard"
%token<fl>              yWIRE           "wire"
%token<fl>              yWITHIN         "within"
%token<fl>              yWITH__BRA      "with-then-["
%token<fl>              yWITH__CUR      "with-then-{"
%token<fl>              yWITH__ETC      "with"
%token<fl>              yWITH__LEX      "with-in-lex"
%token<fl>              yWITH__PAREN    "with-then-("
%token<fl>              yWITH__PAREN_CUR "with-then-(-then-{"
%token<fl>              yWOR            "wor"
%token<fl>              yWREAL          "wreal"
%token<fl>              yXNOR           "xnor"
%token<fl>              yXOR            "xor"

%token<fl>              yD_ACOS         "$acos"
%token<fl>              yD_ACOSH        "$acosh"
%token<fl>              yD_ASIN         "$asin"
%token<fl>              yD_ASINH        "$asinh"
%token<fl>              yD_ASSERTCTL    "$assertcontrol"
%token<fl>              yD_ASSERTFAILOFF "$assertfailoff"
%token<fl>              yD_ASSERTFAILON "$assertfailon"
%token<fl>              yD_ASSERTKILL   "$assertkill"
%token<fl>              yD_ASSERTNONVACUOUSON  "$assertnonvacuouson"
%token<fl>              yD_ASSERTOFF    "$assertoff"
%token<fl>              yD_ASSERTON     "$asserton"
%token<fl>              yD_ASSERTPASSOFF "$assertpassoff"
%token<fl>              yD_ASSERTPASSON  "$assertpasson"
%token<fl>              yD_ASSERTVACUOUSOFF  "$assertvacuousoff"
%token<fl>              yD_ATAN         "$atan"
%token<fl>              yD_ATAN2        "$atan2"
%token<fl>              yD_ATANH        "$atanh"
%token<fl>              yD_BITS         "$bits"
%token<fl>              yD_BITSTOREAL   "$bitstoreal"
%token<fl>              yD_BITSTOSHORTREAL "$bitstoshortreal"
%token<fl>              yD_C            "$c"
%token<fl>              yD_CPURE        "$cpure"
%token<fl>              yD_CAST         "$cast"
%token<fl>              yD_CEIL         "$ceil"
%token<fl>              yD_CHANGED      "$changed"
%token<fl>              yD_CHANGED_GCLK "$changed_gclk"
%token<fl>              yD_CHANGING_GCLK  "$changing_gclk"
%token<fl>              yD_CLOG2        "$clog2"
%token<fl>              yD_COS          "$cos"
%token<fl>              yD_COSH         "$cosh"
%token<fl>              yD_COUNTBITS    "$countbits"
%token<fl>              yD_COUNTONES    "$countones"
%token<fl>              yD_DIMENSIONS   "$dimensions"
%token<fl>              yD_DISPLAY      "$display"
%token<fl>              yD_DISPLAYB     "$displayb"
%token<fl>              yD_DISPLAYH     "$displayh"
%token<fl>              yD_DISPLAYO     "$displayo"
%token<fl>              yD_DIST_CHI_SQUARE "$dist_chi_square"
%token<fl>              yD_DIST_ERLANG  "$dist_erlang"
%token<fl>              yD_DIST_EXPONENTIAL "$dist_exponential"
%token<fl>              yD_DIST_NORMAL  "$dist_normal"
%token<fl>              yD_DIST_POISSON "$dist_poisson"
%token<fl>              yD_DIST_T       "$dist_t"
%token<fl>              yD_DIST_UNIFORM "$dist_uniform"
%token<fl>              yD_DUMPALL      "$dumpall"
%token<fl>              yD_DUMPFILE     "$dumpfile"
%token<fl>              yD_DUMPFLUSH    "$dumpflush"
%token<fl>              yD_DUMPLIMIT    "$dumplimit"
%token<fl>              yD_DUMPOFF      "$dumpoff"
%token<fl>              yD_DUMPON       "$dumpon"
%token<fl>              yD_DUMPPORTS    "$dumpports"
%token<fl>              yD_DUMPVARS     "$dumpvars"
%token<fl>              yD_ERROR        "$error"
%token<fl>              yD_EXIT         "$exit"
%token<fl>              yD_EXP          "$exp"
%token<fl>              yD_FALLING_GCLK "$falling_gclk"
%token<fl>              yD_FATAL        "$fatal"
%token<fl>              yD_FCLOSE       "$fclose"
%token<fl>              yD_FDISPLAY     "$fdisplay"
%token<fl>              yD_FDISPLAYB    "$fdisplayb"
%token<fl>              yD_FDISPLAYH    "$fdisplayh"
%token<fl>              yD_FDISPLAYO    "$fdisplayo"
%token<fl>              yD_FELL         "$fell"
%token<fl>              yD_FELL_GCLK    "$fell_gclk"
%token<fl>              yD_FEOF         "$feof"
%token<fl>              yD_FERROR       "$ferror"
%token<fl>              yD_FFLUSH       "$fflush"
%token<fl>              yD_FGETC        "$fgetc"
%token<fl>              yD_FGETS        "$fgets"
%token<fl>              yD_FINISH       "$finish"
%token<fl>              yD_FLOOR        "$floor"
%token<fl>              yD_FMONITOR     "$fmonitor"
%token<fl>              yD_FMONITORB    "$fmonitorb"
%token<fl>              yD_FMONITORH    "$fmonitorh"
%token<fl>              yD_FMONITORO    "$fmonitoro"
%token<fl>              yD_FOPEN        "$fopen"
%token<fl>              yD_FREAD        "$fread"
%token<fl>              yD_FREWIND      "$frewind"
%token<fl>              yD_FSCANF       "$fscanf"
%token<fl>              yD_FSEEK        "$fseek"
%token<fl>              yD_FSTROBE      "$fstrobe"
%token<fl>              yD_FSTROBEB     "$fstrobeb"
%token<fl>              yD_FSTROBEH     "$fstrobeh"
%token<fl>              yD_FSTROBEO     "$fstrobeo"
%token<fl>              yD_FTELL        "$ftell"
%token<fl>              yD_FUTURE_GCLK  "$future_gclk"
%token<fl>              yD_FWRITE       "$fwrite"
%token<fl>              yD_FWRITEB      "$fwriteb"
%token<fl>              yD_FWRITEH      "$fwriteh"
%token<fl>              yD_FWRITEO      "$fwriteo"
%token<fl>              yD_GLOBAL_CLOCK "$global_clock"
%token<fl>              yD_HIGH         "$high"
%token<fl>              yD_HYPOT        "$hypot"
%token<fl>              yD_INCREMENT    "$increment"
%token<fl>              yD_INFERRED_DISABLE "$inferred_disable"
%token<fl>              yD_INFO         "$info"
%token<fl>              yD_ISUNBOUNDED  "$isunbounded"
%token<fl>              yD_ISUNKNOWN    "$isunknown"
%token<fl>              yD_ITOR         "$itor"
%token<fl>              yD_LEFT         "$left"
%token<fl>              yD_LN           "$ln"
%token<fl>              yD_LOG10        "$log10"
%token<fl>              yD_LOW          "$low"
%token<fl>              yD_MONITOR      "$monitor"
%token<fl>              yD_MONITORB     "$monitorb"
%token<fl>              yD_MONITORH     "$monitorh"
%token<fl>              yD_MONITORO     "$monitoro"
%token<fl>              yD_MONITOROFF   "$monitoroff"
%token<fl>              yD_MONITORON    "$monitoron"
%token<fl>              yD_ONEHOT       "$onehot"
%token<fl>              yD_ONEHOT0      "$onehot0"
%token<fl>              yD_PAST         "$past"
%token<fl>              yD_PAST_GCLK    "$past_gclk"
%token<fl>              yD_POW          "$pow"
%token<fl>              yD_PRINTTIMESCALE "$printtimescale"
%token<fl>              yD_RANDOM       "$random"
%token<fl>              yD_READMEMB     "$readmemb"
%token<fl>              yD_READMEMH     "$readmemh"
%token<fl>              yD_REALTIME     "$realtime"
%token<fl>              yD_REALTOBITS   "$realtobits"
%token<fl>              yD_REWIND       "$rewind"
%token<fl>              yD_RIGHT        "$right"
%token<fl>              yD_RISING_GCLK  "$rising_gclk"
%token<fl>              yD_ROOT         "$root"
%token<fl>              yD_ROSE         "$rose"
%token<fl>              yD_ROSE_GCLK    "$rose_gclk"
%token<fl>              yD_RTOI         "$rtoi"
%token<fl>              yD_SAMPLED      "$sampled"
%token<fl>              yD_SDF_ANNOTATE "$sdf_annotate"
%token<fl>              yD_SETUPHOLD    "$setuphold"
%token<fl>              yD_SFORMAT      "$sformat"
%token<fl>              yD_SFORMATF     "$sformatf"
%token<fl>              yD_SHORTREALTOBITS "$shortrealtobits"
%token<fl>              yD_SIGNED       "$signed"
%token<fl>              yD_SIN          "$sin"
%token<fl>              yD_SINH         "$sinh"
%token<fl>              yD_SIZE         "$size"
%token<fl>              yD_SQRT         "$sqrt"
%token<fl>              yD_SSCANF       "$sscanf"
%token<fl>              yD_STABLE       "$stable"
%token<fl>              yD_STABLE_GCLK  "$stable_gclk"
%token<fl>              yD_STACKTRACE   "$stacktrace"
%token<fl>              yD_STEADY_GCLK  "$steady_gclk"
%token<fl>              yD_STIME        "$stime"
%token<fl>              yD_STOP         "$stop"
%token<fl>              yD_STROBE       "$strobe"
%token<fl>              yD_STROBEB      "$strobeb"
%token<fl>              yD_STROBEH      "$strobeh"
%token<fl>              yD_STROBEO      "$strobeo"
%token<fl>              yD_SWRITE       "$swrite"
%token<fl>              yD_SWRITEB      "$swriteb"
%token<fl>              yD_SWRITEH      "$swriteh"
%token<fl>              yD_SWRITEO      "$swriteo"
%token<fl>              yD_SYSTEM       "$system"
%token<fl>              yD_TAN          "$tan"
%token<fl>              yD_TANH         "$tanh"
%token<fl>              yD_TESTPLUSARGS "$test$plusargs"
%token<fl>              yD_TIME         "$time"
%token<fl>              yD_TIMEFORMAT   "$timeformat"
%token<fl>              yD_TIMEPRECISION "$timeprecision"
%token<fl>              yD_TIMEUNIT     "$timeunit"
%token<fl>              yD_TYPENAME     "$typename"
%token<fl>              yD_UNGETC       "$ungetc"
%token<fl>              yD_UNIT         "$unit"
%token<fl>              yD_UNPACKED_DIMENSIONS "$unpacked_dimensions"
%token<fl>              yD_UNSIGNED     "$unsigned"
%token<fl>              yD_URANDOM      "$urandom"
%token<fl>              yD_URANDOM_RANGE "$urandom_range"
%token<fl>              yD_VALUEPLUSARGS "$value$plusargs"
%token<fl>              yD_WARNING      "$warning"
%token<fl>              yD_WRITE        "$write"
%token<fl>              yD_WRITEB       "$writeb"
%token<fl>              yD_WRITEH       "$writeh"
%token<fl>              yD_WRITEMEMB    "$writememb"
%token<fl>              yD_WRITEMEMH    "$writememh"
%token<fl>              yD_WRITEO       "$writeo"

%token<fl>              yVL_CLOCKER               "/*verilator clocker*/"
%token<fl>              yVL_CLOCK_ENABLE          "/*verilator clock_enable*/"
%token<fl>              yVL_COVERAGE_BLOCK_OFF    "/*verilator coverage_block_off*/"
%token<fl>              yVL_FORCEABLE             "/*verilator forceable*/"
%token<fl>              yVL_FULL_CASE             "/*verilator full_case*/"
%token<fl>              yVL_HIER_BLOCK            "/*verilator hier_block*/"
%token<fl>              yVL_INLINE_MODULE         "/*verilator inline_module*/"
%token<fl>              yVL_ISOLATE_ASSIGNMENTS   "/*verilator isolate_assignments*/"
%token<fl>              yVL_NO_CLOCKER            "/*verilator no_clocker*/"
%token<fl>              yVL_NO_INLINE_MODULE      "/*verilator no_inline_module*/"
%token<fl>              yVL_NO_INLINE_TASK        "/*verilator no_inline_task*/"
%token<fl>              yVL_PARALLEL_CASE         "/*verilator parallel_case*/"
%token<fl>              yVL_PUBLIC                "/*verilator public*/"
%token<fl>              yVL_PUBLIC_FLAT           "/*verilator public_flat*/"
%token<fl>              yVL_PUBLIC_FLAT_ON        "/*verilator public_flat_on*/"
%token<fl>              yVL_PUBLIC_FLAT_RD        "/*verilator public_flat_rd*/"
%token<fl>              yVL_PUBLIC_FLAT_RD_ON     "/*verilator public_flat_rd_on*/"
%token<fl>              yVL_PUBLIC_FLAT_RW        "/*verilator public_flat_rw*/"
%token<fl>              yVL_PUBLIC_FLAT_RW_ON     "/*verilator public_flat_rw_on*/"
%token<fl>              yVL_PUBLIC_FLAT_RW_ON_SNS "/*verilator public_flat_rw_on_sns*/"
%token<fl>              yVL_PUBLIC_ON             "/*verilator public_on*/"
%token<fl>              yVL_PUBLIC_OFF            "/*verilator public_off*/"
%token<fl>              yVL_PUBLIC_MODULE         "/*verilator public_module*/"
%token<fl>              yVL_SC_BIGUINT            "/*verilator sc_biguint*/"
%token<fl>              yVL_SC_BV                 "/*verilator sc_bv*/"
%token<fl>              yVL_SFORMAT               "/*verilator sformat*/"
%token<fl>              yVL_SPLIT_VAR             "/*verilator split_var*/"
%token<strp>            yVL_TAG                   "/*verilator tag*/"
%token<fl>              yVL_UNROLL_DISABLE        "/*verilator unroll_disable*/"
%token<fl>              yVL_UNROLL_FULL           "/*verilator unroll_full*/"

%token<fl>              yP_TICK         "'"
%token<fl>              yP_TICKBRA      "'{"
%token<fl>              yP_OROR         "||"
%token<fl>              yP_ANDAND       "&&"
%token<fl>              yP_NOR          "~|"
%token<fl>              yP_XNOR         "^~"
%token<fl>              yP_NAND         "~&"
%token<fl>              yP_EQUAL        "=="
%token<fl>              yP_NOTEQUAL     "!="
%token<fl>              yP_CASEEQUAL    "==="
%token<fl>              yP_CASENOTEQUAL "!=="
%token<fl>              yP_WILDEQUAL    "==?"
%token<fl>              yP_WILDNOTEQUAL "!=?"
%token<fl>              yP_GTE          ">="
%token<fl>              yP_LTE          "<="
%token<fl>              yP_LTE__IGNORE  "<=-ignored"    // Used when expr:<= means assignment
%token<fl>              yP_SLEFT        "<<"
%token<fl>              yP_SRIGHT       ">>"
%token<fl>              yP_SSRIGHT      ">>>"
%token<fl>              yP_POW          "**"

%token<fl>              yP_COLON__BEGIN ":-then-begin"
%token<fl>              yP_COLON__FORK  ":-then-fork"
%token<fl>              yP_EQ__NEW      "=-then-new"
%token<fl>              yP_PAR__IGNORE  "(-ignored"     // Used when sequence_expr:expr:( is ignored
%token<fl>              yP_PAR__STRENGTH "(-for-strength"

%token<fl>              yP_LTMINUSGT    "<->"
%token<fl>              yP_PLUSCOLON    "+:"
%token<fl>              yP_MINUSCOLON   "-:"
%token<fl>              yP_MINUSGT      "->"
%token<fl>              yP_MINUSGTGT    "->>"
%token<fl>              yP_EQGT         "=>"
%token<fl>              yP_ASTGT        "*>"
%token<fl>              yP_ANDANDAND    "&&&"
%token<fl>              yP_POUNDPOUND   "##"
%token<fl>              yP_POUNDMINUSPD "#-#"
%token<fl>              yP_POUNDEQPD    "#=#"
%token<fl>              yP_DOTSTAR      ".*"

%token<fl>              yP_ATAT         "@@"
%token<fl>              yP_COLONCOLON   "::"
%token<fl>              yP_COLONEQ      ":="
%token<fl>              yP_COLONDIV     ":/"
%token<fl>              yP_ORMINUSGT    "|->"
%token<fl>              yP_OREQGT       "|=>"
%token<fl>              yP_BRASTAR      "[*"
%token<fl>              yP_BRAEQ        "[="
%token<fl>              yP_BRAMINUSGT   "[->"
%token<fl>              yP_BRAPLUSKET   "[+]"

%token<fl>              yP_PLUSPLUS     "++"
%token<fl>              yP_MINUSMINUS   "--"
%token<fl>              yP_PLUSEQ       "+="
%token<fl>              yP_MINUSEQ      "-="
%token<fl>              yP_TIMESEQ      "*="
%token<fl>              yP_DIVEQ        "/="
%token<fl>              yP_MODEQ        "%="
%token<fl>              yP_ANDEQ        "&="
%token<fl>              yP_OREQ         "|="
%token<fl>              yP_XOREQ        "^="
%token<fl>              yP_SLEFTEQ      "<<="
%token<fl>              yP_SRIGHTEQ     ">>="
%token<fl>              yP_SSRIGHTEQ    ">>>="

%token<fl>              yP_PLUSSLASHMINUS "+/-"
%token<fl>              yP_PLUSPCTMINUS "+%-"

// [* is not an operator, as "[ * ]" is legal
// [= and [-> could be repetition operators, but to match [* we don't add them.
// '( is not an operator, as "' (" is legal

//********************
// Verilog op precedence
//UNSUP %token<fl>      prUNARYARITH
//UNSUP %token<fl>      prREDUCTION
//UNSUP %token<fl>      prNEGATION
//UNSUP %token<fl>      prEVENTBEGIN
%token<fl>      prTAGGED

// These prevent other conflicts
%left           yP_ANDANDAND
%left           yMATCHES
%left           prTAGGED
//UNSUP %left   prSEQ_CLOCKING

// PSL op precedence

// Lowest precedence
// These are in IEEE 17.7.1
%nonassoc       yALWAYS yS_ALWAYS yEVENTUALLY yS_EVENTUALLY yACCEPT_ON yREJECT_ON ySYNC_ACCEPT_ON ySYNC_REJECT_ON

%right          yP_ORMINUSGT yP_OREQGT yP_POUNDMINUSPD yP_POUNDEQPD
%right          yUNTIL yS_UNTIL yUNTIL_WITH yS_UNTIL_WITH yIMPLIES
%right          yIFF
%left           yOR
%left           yAND
%nonassoc       yNOT yNEXTTIME yS_NEXTTIME
%left           yINTERSECT
%left           yWITHIN
%right          yTHROUGHOUT
%left           prPOUNDPOUND_MULTI
%left           yP_POUNDPOUND
%left           yP_BRASTAR yP_BRAEQ yP_BRAMINUSGT yP_BRAPLUSKET

// Not specified, but needed higher than yOR, lower than normal non-pexpr expressions
//UNSUP %left           yPOSEDGE yNEGEDGE yEDGE

//UNSUP %left           '{' '}'

// Verilog op precedence
%right          yP_MINUSGT yP_LTMINUSGT
%right          '?' ':' yP_COLON__BEGIN yP_COLON__FORK
%left           yP_OROR
%left           yP_ANDAND
%left           '|' yP_NOR
%left           '^' yP_XNOR
%left           '&' yP_NAND
%left           yP_EQUAL yP_NOTEQUAL yP_CASEEQUAL yP_CASENOTEQUAL yP_WILDEQUAL yP_WILDNOTEQUAL
%left           '>' '<' yP_GTE yP_LTE yP_LTE__IGNORE yINSIDE yDIST
%left           yP_SLEFT yP_SRIGHT yP_SSRIGHT
%left           '+' '-'
%left           '*' '/' '%'
%left           yP_POW
%left           prUNARYARITH yP_MINUSMINUS yP_PLUSPLUS prREDUCTION prNEGATION
%left           '.'
// Not in IEEE, but need to avoid conflicts; TICK should bind tightly just lower than COLONCOLON
%left           yP_TICK
//%left         '(' ')' '[' ']' yP_COLONCOLON '.'

%nonassoc prLOWER_THAN_ELSE
%nonassoc yELSE

//BISONPRE_TYPES
%type<alwaysp>	 assignList assignOne
%type<argp>	 systemDpiArgsE
%type<assertdirectivetypeen>	 assertOrAssume
%type<asserttypeen>	 final_zero
%type<attrtypeen>	 vltVarAttrFront
%type<baseOverride>	 dynamic_override_specifiersE final_specifierE
%type<basicDTypep>	 integer_atom_type integer_vector_type non_integer_type
%type<beginp>	 seq_block seq_blockPreId
%type<caseItemp>	 case_inside_itemList case_itemList property_case_item property_case_itemList rand_case_itemList rs_case_item rs_case_itemList
%type<casep>	 caseStart
%type<cbool>	 classVirtualE colonConfigE constraintStaticE taggedSoftE vltInlineFront
%type<cint>	 funcIsolateE
%type<classExtendsp>	 classExtendsE classExtendsList classExtendsOne classImplementsE classImplementsList
%type<classp>	 classFront
%type<configCellp>	 configCell configCellList design_statement
%type<constp>	 intnumAsConst
%type<constraintp>	 class_constraint constraintIdNew extern_constraint_declaration
%type<delayp>	 cycle_delay cycle_delay_range delay_control delay_controlE
%type<distItemp>	 dist_item dist_list
%type<enumItemp>	 enum_nameList enum_name_declaration
%type<errcodeen>	 vltOffFront vltOnFront
%type<fl>	 bins_keyword colon junkToSemiList
%type<funcp>	 fIdScoped
%type<fwdtype>	 forward_type
%type<genCaseItemp>	 c_case_generate_item c_case_generate_itemList case_generate_item case_generate_itemList
%type<iprop>	 dpi_tf_import_propertyE
%type<joinType>	 par_blockJoin
%type<letp>	 letId let_declaration
%type<lifetime>	 lifetime lifetimeE
%type<memberDTypep>	 list_of_member_decl_assignments member_decl_assignment struct_union_member struct_union_memberList struct_union_memberListEnd
%type<nodeDTypep>	 data_type data_typeAny data_typeBasic data_typeNoRef data_typeVirtual data_type_or_void enumDecl enum_base_typeE implicit_typeE net_dataTypeE property_formal_typeNoDt sequence_formal_typeNoDt simple_typeNoRef type_referenceDecl var_data_type
%type<nodeExprp>	 aliasEqList argsDotted argsDottedList argsExprList argsExprListE argsExprOneE array_methodWith boolean_abbrev caseCondList cateList cgexpr class_new class_newNoScope class_typeExtImpList class_typeExtImpOne clocking_skew clocking_skewE constExpr constraint_primary covergroup_value_range delayExpr delay_value delayed_referenceE dollarUnitNextId dynamic_array_new enumNameStartE expr exprDispList exprE exprEqE exprList exprListE exprNoStr exprOkLvalue exprScope exprTypeCompare fexpr fexprLvalue fexprOkLvalue fexprScope file_path_spec file_path_specList finc_or_dec_expression funcRef function_subroutine_callNoMethod gateAndPinList gateOrPinList gatePinExpr gateUnsupPinList gateXorPinList idArrayed idArrayedForeach idClass idClassSel idClassSelForeach idDotted idDottedForeach idDottedMore idDottedMoreForeach idDottedOrArrayed idDottedSel idDottedSelMore inc_or_dec_expression incdirE inst_name inst_nameInstanceList liblistLibraryList list_of_argumentsE localNextId minTypMax minTypMaxE packageClassScope packageClassScopeE packageClassScopeItem packageClassScopeList packageClassScopeNoId pexpr pexprOkLvalue pexprScope pinc_or_dec_expression property_actual_arg property_statementCaseIf range_list rs_weight_specification sexpr sexprOkLvalue sexprScope sinc_or_dec_expression solve_before_list strAsInt strAsIntIgnore stream_concatenation stream_expression system_f_only_expr_call system_f_or_t_expr_call taskRef task_subroutine_callNoMethod terminal_identifier timeNumAdjusted timing_check_event timing_check_limit type_referenceBoth type_referenceEq value_range variable_lvalue variable_lvalueConcList
%type<nodeFTaskRefp>	 array_methodNoRoot
%type<nodeFTaskp>	 class_constructor_prototype funcId funcIdNew function_declaration function_prototype method_prototype property_declaration property_declarationFront sequence_declaration sequence_declarationFront taskId task_declaration task_prototype
%type<nodeModulep>	 checkerFront checker_declaration intFront modFront packageFront pgmFront udpFront
%type<nodePreSelp>	 part_select_range part_select_rangeList
%type<nodeRangep>	 anyrange instRange instRangeList instRangeListE packed_dimension packed_dimensionList packed_dimensionListE rangeList rangeListE variable_dimension variable_dimensionList variable_dimensionListE
%type<nodeStmtp>	 concurrent_assertion_statement deferred_immediate_assertion_statement foperator_assignment immediate_assertion_statement par_block par_blockPreId procedural_assertion_statement randsequence_statement simple_immediate_assertion_statement statement_item stmt stmtList stmtListE system_t_stmt_call task_subroutine_callNoSemi
%type<nodeStreamp>	 streaming_concatenation
%type<nodeUOrStructDTypep>	 struct_unionDecl
%type<nodep>	 always_construct anonymous_program anonymous_program_item anonymous_program_itemList anonymous_program_itemListE assertion_item assertion_item_declaration assertion_variable_declaration assertion_variable_declarationList bind_directive bind_instantiation bins_expression bins_orBraE bins_or_empty bins_or_options bins_or_optionsList blockDeclListE block_event_expression block_event_expressionTerm block_item_declaration cStrList c_conditional_generate_construct c_genItemBegin c_genItemList c_genItemOrBegin c_generate_block_or_null c_generate_item c_generate_region c_loop_generate_construct cgPortListE checker_generate_item checker_or_generate_item checker_or_generate_itemList checker_or_generate_itemListE checker_or_generate_item_declaration checker_port_item checker_port_itemAssignment checker_port_list checker_port_listE class_constructor_arg class_constructor_arg_listE class_constructor_arg_listList class_declaration class_item class_itemList class_itemListEnd class_method class_property clocking_decl_assign clocking_declaration clocking_item clocking_itemList clocking_itemListE combinational_body commaVRDListE concurrent_assertion_item conditional_generate_construct configParameter configParameterList configParameterListE config_rule_statement config_rule_statementList config_rule_statementListE constraint_block constraint_block_item constraint_block_itemList constraint_expression constraint_expressionList constraint_set continuous_assign cover_cross cover_point coverage_eventE coverage_option coverage_spec_or_option coverage_spec_or_optionList coverage_spec_or_optionListE covergroup_declaration covergroup_range_list cross_body cross_body_item cross_body_itemList cross_item cross_itemList data_declaration defaultDisable deferred_immediate_assertion_item defparam_assignment delay_or_event_controlE dpi_import_export dtypeAttr dtypeAttrList dtypeAttrListE etcInst exprEListE exprOrDataType exprOrDataTypeEqE exprStrText extern_tf_declaration final_construct for_initializationE for_initializationItem for_initializationItemList for_step for_stepE for_step_assignment gateAnd gateAndList gateBuf gateBufList gateBufif0 gateBufif0List gateBufif1 gateBufif1List gateDecl gateFront gateNand gateNandList gateNor gateNorList gateNot gateNotList gateNotif0 gateNotif0List gateNotif1 gateNotif1List gateOr gateOrList gatePulldown gatePulldownList gatePullup gatePullupList gateRangeE gateUnsup gateUnsupList gateXnor gateXnorList gateXor gateXorList genItemBegin genItemList genItemOrBegin generate_block_or_null generate_item generate_region genvar_declaration genvar_initialization genvar_iteration hierarchical_btf_identifier i_genItemBegin i_genItemList i_genItemOrBegin i_generate_region iffE importsAndParametersE include_statement initial_construct instDecl instnameList instnameParen instnameParenUdpn interface_item interface_itemList interface_itemListE interface_or_generate_item let_port_list let_port_listE liblist_clause library_declaration list_of_clocking_decl_assign list_of_cross_items list_of_defparam_assignments list_of_genvar_identifiers list_of_ports list_of_portsE list_of_tf_variable_identifiers loop_generate_construct loop_variableE loop_variables modDefaultClocking modportPortsDecl modportPortsDeclList modportSimplePortOrTFPort modport_declaration modport_item modport_itemList module_common_item module_item module_itemList module_itemListE module_or_generate_item module_or_generate_item_declaration mpInstnameList mpInstnameParen net_alias net_declaration nettype_declaration non_port_module_item non_port_program_item package_export_declaration package_export_item package_export_itemList package_import_declaration package_import_declarationList package_import_item package_import_itemList package_item package_itemList package_itemListE package_itemTop package_or_generate_item_declNoChecker package_or_generate_item_declaration paramPortDeclOrArg paramPortDeclOrArgList paramPortDeclOrArgSub parameter_declaration parameter_port_listE parseRefBase patternKey patternList patternMemberList patternNoExpr patternOne port portAndTag portAndTagE portSig port_declaration portsStarE program_generate_item program_item program_itemList program_itemListE property_declarationBody property_port_item property_port_itemAssignment property_port_list property_port_listE pulldown_strength pulldown_strengthE pullup_strength pullup_strengthE rs_code_block rs_code_blockItem rs_code_blockItemList rs_prod rs_prodList rs_production_item rs_production_itemList select_expression select_expression_r sequence_declarationBody sequence_match_item sequence_match_itemList sequence_port_listE setuphold_timing_check severity_system_task severity_system_task_guts sigAttr sigAttrList sigAttrListE specify_block specify_item specify_itemList specparam_declaration stream_expressionOrDataType system_timing_check tfBodyE tfGuts tfNewGuts tf_item_declaration tf_item_declarationList tf_item_declarationVerilator tf_port_declaration tf_port_item tf_port_listE tf_port_listList timeunits_declaration trans_item trans_list trans_range_list trans_set type_declaration use_clause variable_declExpr vlScBlock vrdList
%type<nump>	 vltDCost vltDLevels vltDWorkers
%type<parseRefp>	 idAnyAsParseRef varRefBase
%type<patMemberp>	 patternMemberOne
%type<patternp>	 assignment_pattern
%type<pinp>	 instParamItList instParamItListE instParamItem instParamListE instPinItListE instPinItemE instPinListE parameter_value_assignmentClass parameter_value_assignmentClassE parameter_value_assignmentInst parameter_value_assignmentInstE useAssignment useAssignmentList useAssignmentListE
%type<pragmap>	 statementVerilatorPragmas
%type<propSpecp>	 property_spec
%type<qualifiers>	 memberQualList memberQualListE memberQualOne random_qualifier random_qualifierE
%type<rSProdListp>	 rs_production_list
%type<rSProdp>	 rs_fId rs_funcId rs_production rs_productionFront rs_productionList
%type<rSRulep>	 rs_rule rs_ruleList
%type<rangep>	 enumNameRangeE
%type<senItemp>	 clocking_event clocking_eventE event_expression senitem senitemEdge senitemVar
%type<senTreep>	 attr_event_control attr_event_controlE event_control
%type<signstate>	 packedSigningE signing signingE
%type<strength>	 strength0 strength1
%type<strengthSpecp>	 driveStrength driveStrengthE
%type<strp>	 bind_target_instance defparamIdRange defparamIdRangeList dpi_importLabelE endLabelE id idAny idAnyE idCC idInst idInstType idNotPathpulse idPathpulse idRandomize idSVKwd idType netId package_import_itemObj startLabelE str vltDBlock vltDContents vltDFTaskE vltDFile vltDHierDpi vltDMatch vltDModel vltDModule vltDModuleE vltDMtask vltDScope vltVarAttrSpecE
%type<udpTableLineValp>	 tableInputList tablelVal
%type<udpTableLinep>	 tableEntryList tableLine
%type<uniqstate>	 unique_priorityE
%type<varp>	 data_declarationVar data_declarationVarClass genvar_identifierDecl let_port_item list_of_param_assignments list_of_specparam_assignments list_of_type_assignments list_of_variable_decl_assignments netSig netSigList param_assignment specparam_assignment tf_port_itemAssignment tf_variable_identifier type_assignment variable_decl_assignment
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion
//  Blank lines for type insertion

%start source_text

%%
//**********************************************************************
// Files

source_text:                    // ==IEEE: source_text
                /* empty */                             { }
        //                      // timeunits_declaration moved into description:package_item
        |       descriptionList                         { }
        ;

descriptionList:                // IEEE: part of source_text
                description                             { }
        |       descriptionList description             { }
        ;

description:                    // ==IEEE: description
                module_declaration                      { }
        //                      // udp_declaration moved into module_declaration
        //                      // library_declaration and include_statement moved from library_description
        |       library_declaration                     { PARSEP->rootp()->addMiscsp($1); }
        |       include_statement                       { }
        |       interface_declaration                   { }
        |       program_declaration                     { }
        |       package_declaration                     { }
        |       package_itemTop                         { if ($1) PARSEP->unitPackage($1->fileline())->addStmtsp($1); }
        |       bind_directive                          { if ($1) PARSEP->unitPackage($1->fileline())->addStmtsp($1); }
        |       config_declaration                      { }
        //                      // Verilator only
        |       yaT_RESETALL                            { }  // Else, under design, and illegal based on IEEE 22.3
        |       yaT_NOUNCONNECTED                       { PARSEP->unconnectedDrive(VOptionBool::OPT_DEFAULT_FALSE); }
        |       yaT_UNCONNECTED_PULL0                   { PARSEP->unconnectedDrive(VOptionBool::OPT_FALSE); }
        |       yaT_UNCONNECTED_PULL1                   { PARSEP->unconnectedDrive(VOptionBool::OPT_TRUE); }
        |       vltItem                                 { }
        |       error                                   { }  // LCOV_EXCL_LINE
        ;

timeunits_declaration:   // ==IEEE: timeunits_declaration
                yTIMEUNIT yaTIMENUM ';'
                        { $$ = PARSEP->createTimescale($<fl>2, true, $2, false, 0); }
        |       yTIMEUNIT yaTIMENUM '/' yaTIMENUM ';'
                        { $$ = PARSEP->createTimescale($<fl>2, true, $2, true, $4); }
        |       yTIMEPRECISION yaTIMENUM ';'
                        { $$ = PARSEP->createTimescale($<fl>2, false, 0, true, $2); }
        ;

//**********************************************************************
// Packages

package_declaration:            // ==IEEE: package_declaration
                packageFront package_itemListE yENDPACKAGE endLabelE
                        { $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));  // Stash for implicit wires, etc
                          if ($2) $1->addStmtsp($2);
                          GRAMMARP->endLabel($<fl>4, $1, $4); }
        ;

packageFront:
                yPACKAGE lifetimeE idAny ';'
                        { $$ = new AstPackage{$<fl>3, *$3, PARSEP->libname()};
                          if ($$->name() == "std") {
                              if ($$->fileline()->filename() != V3Options::getStdPackagePath()) {
                                  $$->v3error("Redeclaring the 'std' package is not allowed");
                              } else {
                                  PARSEP->rootp()->stdPackagep(VN_AS($$, Package));
                              }
                          }
                          $$->inLibrary(true);  // packages are always libraries; don't want to make them a "top"
                          $$->lifetime($2);
                          $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
                          $$->timeunit(PARSEP->timeLastUnit());
                          PARSEP->rootp()->timeprecisionMerge($$->fileline(),
                                                              PARSEP->timeLastPrec());
                          PARSEP->rootp()->addModulesp($$); }
        ;

package_itemListE:       // IEEE: [{ package_item }]
                /* empty */                             { $$ = nullptr; }
        |       package_itemList                        { $$ = $1; }
        ;

package_itemList:        // IEEE: { package_item }
                package_item                            { $$ = $1; }
        |       package_itemList package_item           { $$ = addNextNull($1, $2); }
        ;

package_item:            // ==IEEE: package_item
                package_or_generate_item_declaration    { $$ = $1; }
        |       anonymous_program                       { $$ = $1; }
        |       package_export_declaration              { $$ = $1; }
        |       timeunits_declaration                   { $$ = $1; }
        |       sigAttrScope                            { $$ = nullptr; }
        ;

package_itemTop:         // ==IEEE: package_item

                package_or_generate_item_declNoChecker  { $$ = $1; }
        |       checker_declaration
                       { PARSEP->rootp()->addModulesp($1);
                         $$ = nullptr; }
        |       anonymous_program                       { $$ = $1; }
        |       package_export_declaration              { $$ = $1; }
        |       timeunits_declaration                   { $$ = $1; }
        |       sigAttrScope                            { $$ = nullptr; }
        ;

package_or_generate_item_declaration:    // ==IEEE: package_or_generate_item_declaration
                package_or_generate_item_declNoChecker  { $$ = $1; }
        |       checker_declaration
                        { $1->v3warn(E_UNSUPPORTED, "Unsupported: 'checker' below unit-level");
                          PARSEP->rootp()->addModulesp($1);
                          $$ = nullptr; }
        ;

package_or_generate_item_declNoChecker:
                net_declaration                         { $$ = $1; }
        |       data_declaration                        { $$ = $1; }
        |       task_declaration                        { $$ = $1; }
        |       function_declaration                    { $$ = $1; }
        //                      // IEEE checker_declaration excluded, to handle Top, see other rules
        //                      // checker_declaration
        |       dpi_import_export                       { $$ = $1; }
        |       extern_constraint_declaration           { $$ = $1; }
        |       class_declaration                       { $$ = $1; }
        //                      // IEEE-2023: Added: interface_class_declaration
        //                      // interface_class_declaration is part of class_declaration
        //                      // class_constructor_declaration is part of function_declaration
        //                      // local_parameter_declaration under parameter_declaration
        |       parameter_declaration ';'               { $$ = $1; }
        |       covergroup_declaration                  { $$ = $1; }
        |       assertion_item_declaration              { $$ = $1; }
        |       ';'                                     { $$ = nullptr; }
        ;

package_import_declarationList:
                package_import_declaration              { $$ = $1; }
        |       package_import_declarationList package_import_declaration
                        { $$ = addNextNull($1, $2); }
        ;

package_import_declaration:      // ==IEEE: package_import_declaration
                yIMPORT package_import_itemList ';'     { $$ = $2; }
        ;

package_import_itemList:
                package_import_item                     { $$ = $1; }
        |       package_import_itemList ',' package_import_item { $$ = addNextNull($1, $3); }
        ;

package_import_item:     // ==IEEE: package_import_item
                idCC/*package_identifier*/ yP_COLONCOLON package_import_itemObj
                        { $$ = new AstPackageImport{$<fl>1, *$<strp>1, *$3}; }
        ;

package_import_itemObj:   // IEEE: part of package_import_item
                idAny/*package_identifier*/             { $<fl>$ = $<fl>1; $$ = $1; }
        |       '*'                                     { $<fl>$ = $<fl>1; static string star = "*"; $$ = &star; }
        ;

package_export_declaration: // IEEE: package_export_declaration
                yEXPORT '*' yP_COLONCOLON '*' ';'
                        { $$ = new AstPackageExportStarStar{$<fl>2}; }
        |       yEXPORT package_export_itemList ';'     { $$ = $2; }
        ;

package_export_itemList:
                package_export_item                     { $$ = $1; }
        |       package_export_itemList ',' package_export_item { $$ = addNextNull($1, $3); }
        ;

package_export_item:     // ==IEEE: package_export_item
                idCC yP_COLONCOLON package_import_itemObj
                        { $$ = new AstPackageExport{$<fl>3, *$<strp>1, *$3}; }
        ;

//**********************************************************************
// Module headers

module_declaration:             // ==IEEE: module_declaration
        //                      // timeunits_declaration instead in module_item
        //                      // IEEE: module_nonansi_header + module_ansi_header
                modFront importsAndParametersE portsStarE ';'
        /*cont*/    module_itemListE yENDMODULE endLabelE
                        { $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));  // Stash for implicit wires, etc
                          $1->hasParameterList($<flag>2);
                          if ($2) $1->addStmtsp($2);
                          if ($3) $1->addStmtsp($3);
                          if ($5) $1->addStmtsp($5);
                          GRAMMARP->endLabel($<fl>7, $1, $7); }
        |       udpFront portsStarE ';'
        /*cont*/    module_itemListE yENDPRIMITIVE endLabelE
                        { $1->modTrace(false);  // Stash for implicit wires, etc
                          if ($2) $1->addStmtsp($2);
                          if ($4) $1->addStmtsp($4);
                          GRAMMARP->m_tracingParse = true;
                          GRAMMARP->endLabel($<fl>6, $1, $6); }
        //
        |       yEXTERN modFront parameter_port_listE portsStarE ';'
                        { BBUNSUP($<fl>1, "Unsupported: extern module"); }
        ;

modFront:
        //                      // General note: all *Front functions must call symPushNew before
        //                      // any formal arguments, as the arguments must land in the new scope.
                yMODULE lifetimeE idAny
                        { $$ = new AstModule{$<fl>3, *$3, PARSEP->libname()};
                          $$->lifetime($2);
                          $$->inLibrary(PARSEP->inLibrary() || $$->fileline()->celldefineOn());
                          $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
                          $$->timeunit(PARSEP->timeLastUnit());
                          PARSEP->rootp()->timeprecisionMerge($$->fileline(),
                                                              PARSEP->timeLastPrec());
                          $$->unconnectedDrive(PARSEP->unconnectedDrive());
                          PARSEP->rootp()->addModulesp($$); }
        |       modFront sigAttrScope                   { $$ = $1; }
        ;

importsAndParametersE:   // IEEE: common part of module_declaration, interface_declaration, program_declaration
        //                      // { package_import_declaration } [ parameter_port_list ]
                parameter_port_listE
                        { $$ = $1; $<flag>$ = $<flag>1; }  // hasParameterList
        |       package_import_declarationList parameter_port_listE
                        { $$ = addNextNull($1, $2);
                          $<flag>$ = $<flag>2; }  // hasParameterList
        ;

udpFront:
                yPRIMITIVE lifetimeE idAny
                        { $$ = new AstPrimitive{$<fl>3, *$3, PARSEP->libname()};
                          $$->inLibrary(true);
                          $$->lifetime($2);
                          $$->modTrace(false);
                          $$->addStmtsp(new AstPragma{$<fl>3, VPragmaType::INLINE_MODULE});
                          GRAMMARP->m_tracingParse = false;
                          PARSEP->rootp()->addModulesp($$); }
        ;

parameter_value_assignmentInstE:      // IEEE: [ parameter_value_assignment ] for instance
                /* empty */                             { $$ = nullptr; }
        |       parameter_value_assignmentInst          { $$ = $1; }
        ;

parameter_value_assignmentClassE:      // IEEE: [ parameter_value_assignment ] for classes
                /* empty */                             { $$ = nullptr; }
        |       parameter_value_assignmentClass         { $$ = $1; }
        ;

parameter_value_assignmentInst:       // IEEE: parameter_value_assignment for instance
                '#' '(' instParamListE ')'              { $$ = $3; }
        //                      // Parentheses are optional around a single parameter
        //                      // IMPORTANT: Below hardcoded in tokenPipeScanParam
        |       '#' yaINTNUM                            { $$ = new AstPin{$<fl>2, 1, "", new AstConst{$<fl>2, *$2}}; }
        |       '#' yaFLOATNUM                          { $$ = new AstPin{$<fl>2, 1, "",
                                                                          new AstConst{$<fl>2, AstConst::RealDouble{}, $2}}; }
        |       '#' timeNumAdjusted                     { $$ = new AstPin{$<fl>2, 1, "", $2}; }
        |       '#' idClassSel                          { $$ = new AstPin{$<fl>2, 1, "", $2}; }
        //                      // Not needed in Verilator:
        //                      // Side effect of combining *_instantiations
        //                      // '#' delay_value      { UNSUP }
        ;

parameter_value_assignmentClass:  // IEEE: parameter_value_assignment (for classes)
        //                      // Like parameter_value_assignment, but for classes only, which always have #()
                '#' '(' instParamListE ')'              { $$ = $3; }
        ;

parameter_port_listE:    // IEEE: parameter_port_list + empty == parameter_value_assignment
                /* empty */                             { $$ = nullptr; $<flag>$ = false; }  // hasParameterList
        |       '#' '(' ')'                             { $$ = nullptr;
                                                          $<flag>$ = true; }  // hasParameterList
        //                      // IEEE: '#' '(' list_of_param_assignments { ',' parameter_port_declaration } ')'
        //                      // IEEE: '#' '(' parameter_port_declaration { ',' parameter_port_declaration } ')'
        //                      // Can't just do that as "," conflicts with between vars and between stmts, so
        //                      // split into pre-comma and post-comma parts
        |       '#' '('                                 { VARRESET_LIST(GPARAM);
                                                          GRAMMARP->m_pinAnsi = true; }
        /*cont*/    paramPortDeclOrArgList ')'          { $$ = $4;
                                                          $<flag>$ = true;  // hasParameterList
                                                          VARRESET_NONLIST(UNKNOWN);
                                                          GRAMMARP->m_pinAnsi = false; }
        //                      // Note legal to start with "a=b" with no parameter statement
        ;

paramPortDeclOrArgList:  // IEEE: list_of_param_assignments + { parameter_port_declaration }
                paramPortDeclOrArg                              { $$ = $1; }
        |       paramPortDeclOrArgList ',' paramPortDeclOrArg   { $$ = $1->addNext($3); }
        |       paramPortDeclOrArgList sigAttrScope             { $$ = $1; }
        ;

paramPortDeclOrArg:      // IEEE: param_assignment + parameter_port_declaration
        //                      // We combine the two as we can't tell which follows a comma
                paramPortDeclOrArgSub                   { $$ = $1; }
        |       vlTag                                   { $$ = nullptr; }
        ;

paramPortDeclOrArgSub:
                parameter_port_declarationFrontE param_assignment       { $$ = $2; }
        |       parameter_port_declarationTypeFrontE type_assignment    { $$ = $2; }
        |       sigAttrScope paramPortDeclOrArgSub                      { $$ = $2; }
        ;

portsStarE:              // IEEE: .* + list_of_ports + list_of_port_declarations + empty
                /* empty */                             { $$ = nullptr; }
        |       '(' ')'                                 { $$ = nullptr; }
        //                      // .* expanded from module_declaration
        //UNSUP '(' yP_DOTSTAR ')'                              { UNSUP }
        |       '('
        /*mid*/         { VARRESET_LIST(PORT); GRAMMARP->m_pinAnsi = true; }
        /*cont*/    list_of_ports ')'
                       { $$ = $3; VARRESET_NONLIST(UNKNOWN); GRAMMARP->m_pinAnsi = false; }
        ;

list_of_portsE:          // IEEE: [ list_of_ports + list_of_port_declarations ]
                portAndTagE                             { $$ = $1; }
        |       list_of_portsE ',' portAndTagE          { $$ = addNextNull($1, $3); }
        ;

list_of_ports:           // IEEE: list_of_ports + list_of_port_declarations
                portAndTag                              { $$ = $1; }
        |       list_of_portsE ',' portAndTagE          { $$ = addNextNull($1, $3); }
        ;

portAndTagE:
                /* empty */
                        { const int p = PINNUMINC();
                          const string name = "__pinNumber" + cvtToStr(p);
                          $$ = new AstPort{CRELINE(), p, name};
                          AstVar* varp = new AstVar{CRELINE(), VVarType::WIRE, name, VFlagChildDType{},
                                                    new AstBasicDType{CRELINE(), LOGIC_IMPLICIT}};
                          varp->declDirection(VDirection::INPUT);
                          varp->direction(VDirection::INPUT);
                          varp->ansi(false);
                          varp->declTyped(true);
                          varp->trace(false);
                          $$ = $$->addNext(varp);
                          $$->v3warn(NULLPORT, "Null port on module (perhaps extraneous comma)"); }
        |       portAndTag                              { $$ = $1; }
        |       portAndTag sigAttrScope                 { $$ = $1; }
        ;

portAndTag:
                port                                    { $$ = $1; }
        |       vlTag port                              { $$ = $2; }  // Tag will associate with previous port
        |       sigAttrScope portAndTag                 { $$ = $2; }
        ;

port:                    // ==IEEE: port
        //                      // SEE ALSO port_declaration, tf_port_declaration,
        //                      // data_declarationVarFront
        //
        //                      // Though not type for interfaces, we factor out the port direction and type
        //                      // so we can handle it in one place
        //
        //                      // IEEE: interface_port_header port_identifier { unpacked_dimension }
        //                      // Expanded interface_port_header
        //                      // We use instantCb here because the non-port form looks just like a module instantiation
        //
        //                      // Looks identical to variable_declaration, so V3LinkDot must resolve when ID known
        //                      // NO: portDirNetE id/*interface*/ portSig variable_dimensionListE sigAttrListE
        //
                portDirNetE id/*interface*/ '.' idAny/*modport*/ portSig variable_dimensionListE sigAttrListE
                        { // VAR for now, but V3LinkCells may call setIfcaeRef on it later
                          $$ = $5; VARDECL(VAR); VARIO(NONE);
                          AstNodeDType* const dtp = new AstIfaceRefDType{$<fl>2, $<fl>4, "", *$2, *$4};
                          VARDTYPE(dtp); VARIOANSI();
                          addNextNull($$, VARDONEP($$, $6, $7)); }
        |       portDirNetE yINTERFACE                           portSig rangeListE sigAttrListE
                        { $$ = $3; GRAMMARP->createGenericIface($3, $4, $5); }
        |       portDirNetE yINTERFACE      '.' idAny/*modport*/ portSig rangeListE sigAttrListE
                        { $$ = $5; GRAMMARP->createGenericIface($5, $6, $7, $<fl>4, *$4); }
        //
        |       portDirNetE yINTERCONNECT signingE rangeListE portSig variable_dimensionListE sigAttrListE
                        { $$ = $5;
                          BBUNSUP($<fl>2, "Unsupported: interconnect");
                          AstNodeDType* const dtp = GRAMMARP->addRange(
                                    new AstBasicDType{$2, LOGIC_IMPLICIT, $3}, $4, true);
                          VARDTYPE(dtp); VARIOANSI();
                          addNextNull($$, VARDONEP($$, $6, $7)); }
        //
        //                      // IEEE: ansi_port_declaration, with [port_direction] removed
        //                      //   IEEE: [ net_port_header | interface_port_header ]
        //                      //         port_identifier { unpacked_dimension } [ '=' constant_expression ]
        //                      //   IEEE: [ net_port_header | variable_port_header ] '.' port_identifier '(' [ expression ] ')'
        //                      //   IEEE: [ variable_port_header ] port_identifier
        //                      //              { variable_dimension } [ '=' constant_expression ]
        //                      //   Substitute net_port_header = [ port_direction ] net_port_type
        //                      //   Substitute variable_port_header = [ port_direction ] variable_port_type
        //                      //   Substitute net_port_type = [ net_type ] data_type_or_implicit
        //                      //   Substitute variable_port_type = var_data_type
        //                      //   Substitute var_data_type = data_type | yVAR data_type_or_implicit
        //                      //     [ [ port_direction ] net_port_type | interface_port_header]
        //                      //              port_identifier { unpacked_dimension }
        //                      //     [ [ port_direction ] var_data_type ]
        //                      //              port_identifier variable_dimensionListE [ '=' constant_expression ]
        //                      //     [ [ port_direction ] net_port_type | [ port_direction ] var_data_type ]
        //                      //              '.' port_identifier '(' [ expression ] ')'
        //
        //                      // Remove optional '[...] id' is in portAssignment
        //                      // Remove optional '[port_direction]' is in port
        //                      //     net_port_type | interface_port_header
        //                      //            port_identifier { unpacked_dimension }
        //                      //     net_port_type | interface_port_header
        //                      //            port_identifier { unpacked_dimension }
        //                      //     var_data_type
        //                      //            port_identifier variable_dimensionListE [ '=' constExpr ]
        //                      //     net_port_type | [ port_direction ] var_data_type '.' port_identifier '(' [ expr ] ')'
        //                      // Expand implicit_type
        //
        //                      // variable_dimensionListE instead of rangeListE to avoid conflicts
        //
        //                      // Note implicit rules looks just line declaring additional followon port
        //                      // No VARDECL("port") for implicit, as we don't want to declare variables for them
        //                      // IEEE: portDirNetE data_type '.' portSig -> handled with AstDot in expr.
        //
        |       portDirNetE data_type           portSig variable_dimensionListE sigAttrListE
                        { $$ = $3; VARDTYPE($2); VARIOANSI();
                          addNextNull($$, VARDONEP($$, $4, $5)); }
        |       portDirNetE data_type           portSig variable_dimensionListE sigAttrListE '=' constExpr
                        { $$ = $3; VARDTYPE($2); VARIOANSI();
                          if (AstVar* vp = VARDONEP($$, $4, $5)) { addNextNull($$, vp); vp->valuep($7); } }
        |       portDirNetE yVAR data_type      portSig variable_dimensionListE sigAttrListE
                        { $$ = $4; VARDTYPE($3); VARIOANSI();
                          addNextNull($$, VARDONEP($$, $5, $6)); }
        |       portDirNetE yVAR data_type      portSig variable_dimensionListE sigAttrListE '=' constExpr
                        { $$ = $4; VARDTYPE($3); VARIOANSI();
                          if (AstVar* vp = VARDONEP($$, $5, $6)) { addNextNull($$, vp); vp->valuep($8); } }
        |       portDirNetE yVAR implicit_typeE portSig variable_dimensionListE sigAttrListE
                        { $$ = $4; VARDTYPE($3); VARIOANSI();
                          addNextNull($$, VARDONEP($$, $5, $6)); }
        |       portDirNetE yVAR implicit_typeE portSig variable_dimensionListE sigAttrListE '=' constExpr
                        { $$ = $4; VARDTYPE($3); VARIOANSI();
                          if (AstVar* vp = VARDONEP($$, $5, $6)) { addNextNull($$, vp); vp->valuep($8); } }
        |       portDirNetE signing             portSig variable_dimensionListE sigAttrListE
                        { $$ = $3;
                          AstNodeDType* const dtp = new AstBasicDType{$3->fileline(), LOGIC_IMPLICIT, $2};
                          VARDTYPE_NDECL(dtp); VARIOANSI();
                          addNextNull($$, VARDONEP($$, $4, $5)); }
        |       portDirNetE signing             portSig variable_dimensionListE sigAttrListE '=' constExpr
                        { $$ = $3;
                          AstNodeDType* const dtp = new AstBasicDType{$3->fileline(), LOGIC_IMPLICIT, $2};
                          VARDTYPE_NDECL(dtp); VARIOANSI();
                          if (AstVar* vp = VARDONEP($$, $4, $5)) { addNextNull($$, vp); vp->valuep($7); } }
        |       portDirNetE signingE rangeList  portSig variable_dimensionListE sigAttrListE
                        { $$ = $4;
                          AstNodeDType* const dtp = GRAMMARP->addRange(
                                    new AstBasicDType{$3->fileline(), LOGIC_IMPLICIT, $2}, $3, true);
                          VARDTYPE_NDECL(dtp);
                          addNextNull($$, VARDONEP($$, $5, $6)); }
        |       portDirNetE signingE rangeList  portSig variable_dimensionListE sigAttrListE '=' constExpr
                        { $$ = $4;
                          AstNodeDType* const dtp = GRAMMARP->addRange(
                                    new AstBasicDType{$3->fileline(), LOGIC_IMPLICIT, $2}, $3, true);
                          VARDTYPE_NDECL(dtp);
                          if (AstVar* vp = VARDONEP($$, $5, $6)) { addNextNull($$, vp); vp->valuep($8); } }
        |       portDirNetE /*implicit*/        portSig variable_dimensionListE sigAttrListE
                        { $$ = $2; /*VARDTYPE-same*/ addNextNull($$, VARDONEP($$, $3, $4)); }
        |       portDirNetE /*implicit*/        portSig variable_dimensionListE sigAttrListE '=' constExpr
                        { $$ = $2; /*VARDTYPE-same*/
                          if (AstVar* vp = VARDONEP($$, $3, $4)) { addNextNull($$, vp); vp->valuep($6); } }
        ;

portDirNetE:                    // IEEE: part of port, optional net type and/or direction
                /* empty */                             { }
        //                      // Per spec, if direction given default the nettype.
        //                      // The higher level rule may override this VARDTYPE with one later in the parse.
        |       port_direction                                  { VARDECL(PORT); VARDTYPE_NDECL(nullptr); }
        |       port_direction { VARDECL(PORT); } net_type      { VARDTYPE_NDECL(nullptr); }  // net_type calls VARDECL
        |       net_type                                        { VARDTYPE_NDECL(nullptr); }  // net_type calls VARDECL
        ;

port_declNetE:                  // IEEE: part of port_declaration, optional net type
                /* empty */                             { }
        |       net_type                                { } // net_type calls VARDECL
        ;

portSig:
                id/*port*/
                        { $$ = new AstPort{$<fl>1, PINNUMINC(), *$1}; }
        |       idSVKwd
                        { $$ = new AstPort{$<fl>1, PINNUMINC(), *$1}; }
        ;

//**********************************************************************
// Interface headers

interface_declaration:          // IEEE: interface_declaration + interface_nonansi_header + interface_ansi_header:
        //                      // timeunits_declarationE is instead in interface_item
                intFront importsAndParametersE portsStarE ';'
                        interface_itemListE yENDINTERFACE endLabelE
                        { if ($2) $1->addStmtsp($2);
                          if ($3) $1->addStmtsp($3);
                          if ($5) $1->addStmtsp($5);
                          $1->hasParameterList($<flag>2); }
        |       yEXTERN intFront parameter_port_listE portsStarE ';'
                        { BBUNSUP($<fl>1, "Unsupported: extern interface"); }
        ;

intFront:
                yINTERFACE lifetimeE idAny/*new_interface*/
                        { $$ = new AstIface{$<fl>3, *$3, PARSEP->libname()};
                          $$->inLibrary(true);
                          $$->lifetime($2);
                          PARSEP->rootp()->addModulesp($$); }
        |       intFront sigAttrScope                   { $$ = $1; }
        ;

interface_itemListE:
                /* empty */                             { $$ = nullptr; }
        |       interface_itemList                      { $$ = $1; }
        ;

interface_itemList:
                interface_item                          { $$ = $1; }
        |       interface_itemList interface_item       { $$ = addNextNull($1, $2); }
        ;

interface_item:          // IEEE: interface_item + non_port_interface_item
                port_declaration ';'                    { $$ = $1; }
        //                      // IEEE: non_port_interface_item
        //                      // IEEE: generate_region
        |       i_generate_region                       { $$ = $1; }
        |       interface_or_generate_item              { $$ = $1; }
        |       program_declaration
                        { $$ = nullptr; BBUNSUP(CRELINE(), "Unsupported: program decls within interface decls"); }
        //                      // IEEE 1800-2017: modport_item
        //                      // See instead old 2012 position in interface_or_generate_item
        |       interface_declaration
                        { $$ = nullptr; BBUNSUP(CRELINE(), "Unsupported: interface decls within interface decls"); }
        |       timeunits_declaration                   { $$ = $1; }
        //                      // See note in interface_or_generate item
        |       module_common_item                      { $$ = $1; }
        ;

interface_or_generate_item:  // ==IEEE: interface_or_generate_item
        //                      // module_common_item in interface_item, as otherwise duplicated
        //                      // with module_or_generate_item's module_common_item
                modport_declaration                     { $$ = $1; }
        |       extern_tf_declaration                   { $$ = $1; }
        ;

//**********************************************************************
// Program headers

anonymous_program:       // ==IEEE: anonymous_program
        //                      // See the spec - this doesn't change the scope, items still go up "top"
                yPROGRAM ';' anonymous_program_itemListE yENDPROGRAM
                        { $$ = nullptr;
                         BBUNSUP($<fl>1, "Unsupported: Anonymous programs");
                         VARDTYPE_NDECL(nullptr);
                         DEL($3); }
        ;

anonymous_program_itemListE:     // IEEE: { anonymous_program_item }
                /* empty */                             { $$ = nullptr; }
        |       anonymous_program_itemList              { $$ = $1; }
        ;

anonymous_program_itemList:      // IEEE: { anonymous_program_item }
                anonymous_program_item                  { $$ = $1; }
        |       anonymous_program_itemList anonymous_program_item       { $$ = addNextNull($1, $2); }
        ;

anonymous_program_item:  // ==IEEE: anonymous_program_item
                task_declaration                        { $$ = $1; }
        |       function_declaration                    { $$ = $1; }
        |       class_declaration                       { $$ = $1; }
        //                      // IEEE-2023: Added: interface_class_declaration
        //                      // interface_class_declaration is part of class_declaration
        |       covergroup_declaration                  { $$ = $1; }
        //                      // class_constructor_declaration is part of function_declaration
        |       ';'                                     { $$ = nullptr; }
        ;

program_declaration:            // IEEE: program_declaration + program_nonansi_header + program_ansi_header:
        //                      // timeunits_declarationE is instead in program_item
                pgmFront parameter_port_listE portsStarE ';'
        /*cont*/    program_itemListE yENDPROGRAM endLabelE
                        { $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));  // Stash for implicit wires, etc
                          $1->hasParameterList($<flag>2);
                          if ($2) $1->addStmtsp($2);
                          if ($3) $1->addStmtsp($3);
                          if ($5) $1->addStmtsp($5);
                          GRAMMARP->endLabel($<fl>7, $1, $7); }
        |       yEXTERN pgmFront parameter_port_listE portsStarE ';'
                        { BBUNSUP($<fl>1, "Unsupported: extern program"); }
        ;

pgmFront:
                yPROGRAM lifetimeE idAny/*new_program*/
                        { $$ = new AstModule{$<fl>3, *$3, PARSEP->libname(), AstModule::Program{}};
                          $$->lifetime($2);
                          $$->inLibrary(PARSEP->inLibrary() || $$->fileline()->celldefineOn());
                          $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
                          $$->timeunit(PARSEP->timeLastUnit());
                          PARSEP->rootp()->timeprecisionMerge($$->fileline(),
                                                              PARSEP->timeLastPrec());
                          PARSEP->rootp()->addModulesp($$); }
        ;

program_itemListE:       // ==IEEE: [{ program_item }]
                /* empty */                             { $$ = nullptr; }
        |       program_itemList                        { $$ = $1; }
        ;

program_itemList:        // ==IEEE: { program_item }
                program_item                            { $$ = $1; }
        |       program_itemList program_item           { $$ = addNextNull($1, $2); }
        ;

program_item:            // ==IEEE: program_item
                port_declaration ';'                    { $$ = $1; }
        |       non_port_program_item                   { $$ = $1; }
        ;

non_port_program_item:   // ==IEEE: non_port_program_item
                continuous_assign                       { $$ = $1; }
        |       module_or_generate_item_declaration     { $$ = $1; }
        |       initial_construct                       { $$ = $1; }
        |       final_construct                         { $$ = $1; }
        |       concurrent_assertion_item               { $$ = $1; }
        |       timeunits_declaration                   { $$ = $1; }
        |       program_generate_item                   { $$ = $1; }
        ;

program_generate_item:           // ==IEEE: program_generate_item
                loop_generate_construct                 { $$ = $1; }
        |       conditional_generate_construct          { $$ = $1; }
        |       generate_region                         { $$ = $1; }
                                // not in IEEE, but presumed so can do yBEGIN ... yEND
        |       genItemBegin                            { $$ = $1; }
        |       severity_system_task                    { $$ = $1; }
        ;

extern_tf_declaration:           // ==IEEE: extern_tf_declaration
                yEXTERN task_prototype ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: extern task"); DEL($2); }
        |       yEXTERN function_prototype ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: extern function"); DEL($2); }
        |       yEXTERN yFORKJOIN task_prototype ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: extern forkjoin"); DEL($3); }
        ;

modport_declaration:             // ==IEEE: modport_declaration
                yMODPORT modport_itemList ';'           { $$ = $2; }
        ;

modport_itemList:                // IEEE: part of modport_declaration
                modport_item                            { $$ = $1; }
        |       modport_itemList ',' modport_item       { $$ = addNextNull($1, $3); }
        ;

modport_item:                    // ==IEEE: modport_item
                idAny/*new-modport*/ '('
        /*mid*/         { VARRESET_NONLIST(UNKNOWN); VARIO(INOUT); }
        /*cont*/    modportPortsDeclList ')'            { $$ = new AstModport{$<fl>1, *$1, $4}; }
        ;

modportPortsDeclList:
                modportPortsDecl                            { $$ = $1; }
        |       modportPortsDeclList ',' modportPortsDecl   { $$ = addNextNull($1, $3); }
        ;

// IEEE: modport_ports_declaration  + modport_simple_ports_declaration
//      + (modport_tf_ports_declaration+import_export) + modport_clocking_declaration
// We've expanded the lists each take to instead just have standalone ID ports.
// We track the type as with the V2k series of defines, then create as each ID is seen.
modportPortsDecl:
        //                      // IEEE: modport_simple_ports_declaration
                port_direction { GRAMMARP->m_modportImpExpActive = false; } modportSimplePortOrTFPort { $$ = $3; }
        //                      // IEEE: modport_clocking_declaration
        |       yCLOCKING idAny/*clocking_identifier*/ { $$ = new AstModportClockingRef{$1, *$2}; }
        //                      // IEEE: yIMPORT modport_tf_port
        //                      // IEEE: yEXPORT modport_tf_port
        //                      // modport_tf_port expanded here
        |       yIMPORT idAny/*tf_identifier*/
                        { $$ = new AstModportFTaskRef{$<fl>2, *$2, false};
                          GRAMMARP->m_modportImpExpActive = true;
                          GRAMMARP->m_modportImpExpLastIsExport = false; }
        |       yEXPORT idAny/*tf_identifier*/
                        { $$ = new AstModportFTaskRef{$<fl>2, *$2, true};
                          GRAMMARP->m_modportImpExpActive = true;
                          GRAMMARP->m_modportImpExpLastIsExport = true; }
        |       yIMPORT method_prototype
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: Modport import with prototype"); DEL($2); }
        |       yEXPORT method_prototype
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: Modport export with prototype"); DEL($2); }
        // Continuations of above after a comma.
        //                      // IEEE: modport_simple_ports_declaration
        |       modportSimplePortOrTFPort                { $$ = $1; }
        ;

modportSimplePortOrTFPort:// IEEE: modport_simple_port or modport_tf_port, depending what keyword was earlier
                idAny                                   { $$ = GRAMMARP->m_modportImpExpActive ?
                                                                static_cast<AstNode*>(
                                                                  new AstModportFTaskRef{
                                                                    $<fl>1, *$1, GRAMMARP->m_modportImpExpLastIsExport} ) :
                                                                static_cast<AstNode*>(
                                                                  new AstModportVarRef{
                                                                    $<fl>1, *$1, GRAMMARP->m_varIO} ); }
        |       '.' idAny '(' ')'                       { $$ = new AstModportVarRef{$<fl>2, *$2, GRAMMARP->m_varIO};
                                                          BBUNSUP($<fl>4, "Unsupported: Modport empty expression"); }
        |       '.' idAny '(' expr ')'                  { $$ = new AstModportVarRef{$<fl>2, *$2, $4, GRAMMARP->m_varIO}; }
        ;

//************************************************
// Variable Declarations

genvar_declaration:      // ==IEEE: genvar_declaration
                yGENVAR list_of_genvar_identifiers ';'  { $$ = $2; }
        ;

list_of_genvar_identifiers:      // IEEE: list_of_genvar_identifiers (for declaration)
                genvar_identifierDecl                   { $$ = $1; }
        |       list_of_genvar_identifiers ',' genvar_identifierDecl    { $$ = $1->addNext($3); }
        ;

genvar_identifierDecl:            // IEEE: genvar_identifier (for declaration)
                idAny/*new-genvar_identifier*/ sigAttrListE
                        { VARRESET_NONLIST(GENVAR);
                          AstNodeDType* const dtp = new AstBasicDType{$<fl>1, VBasicDTypeKwd::INTEGER};
                          VARDTYPE(dtp);
                          $$ = VARDONEA($<fl>1, *$1, nullptr, $2); }
        ;

parameter_declaration:   // IEEE: local_ or parameter_declaration and type_parameter_declaration
        //                      // IEEE: yPARAMETER yTYPE list_of_type_assignments ';'
        //                      // Instead of list_of_type_assignments
        //                      // we use list_of_param_assignments because for port handling
        //                      // it already must accept types, so simpler to have code only one place
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                parameter_declarationFront list_of_param_assignments            { $$ = $2; }
        |       parameter_declarationTypeFront list_of_type_assignments         { $$ = $2; }
        ;

parameter_declarationFront:     // IEEE: local_ or parameter_declaration w/o assignment
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                varParamReset implicit_typeE            { /*VARRESET-in-varParam*/ VARDTYPE($2); }
        |       varParamReset data_type                 { /*VARRESET-in-varParam*/ VARDTYPE($2); }
        ;

parameter_declarationTypeFront: // IEEE: local_ or parameter_declaration w/o assignment
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                varParamReset yTYPE__ETC
                        { /*VARRESET-in-varParam*/ VARDTYPE(new AstParseTypeDType{$2}); }
        |       varParamReset yTYPE__ETC forward_type
                        { /*VARRESET-in-varParam*/
                          AstNodeDType* const dtp = new AstParseTypeDType{$2, $3}; VARDTYPE(dtp); }
        ;

parameter_port_declarationFrontE: // IEEE: local_ or parameter_port_declaration w/o assignment
        //                      // IEEE: parameter_declaration (minus assignment)
        //                      // IEEE: local_parameter_declaration (minus assignment)
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                varParamReset implicit_typeE            { /*VARRESET-in-varParam*/ VARDTYPE($2); }
        |       varParamReset data_type                 { /*VARRESET-in-varParam*/ VARDTYPE($2); }
        |       implicit_typeE
                        { /*VARRESET-in-varParam*/
                          // Keep previous type to handle subsequent declarations.
                          // This rule is also used when the previous parameter is a type parameter
                          if ($1) $1->v3error("parameter port declarations require 'parameter'"
                                              " keyword before implicit data types"
                                              " (IEEE 1800-2023 6.20.1/A.2.1.1)\n"
                                              + $1->warnMore()
                                              + "... Suggest add 'parameter' before here");
                       }
        |       data_type                               { /*VARRESET-in-varParam*/ VARDTYPE($1); }
        ;

parameter_port_declarationTypeFrontE: // IEEE: parameter_port_declaration w/o assignment
        //                      // IEEE: parameter_declaration (minus assignment)
        //                      // IEEE: local_parameter_declaration (minus assignment)
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                varParamReset yTYPE__ETC
                        { /*VARRESET-in-varParam*/
                          AstNodeDType* const dtp = new AstParseTypeDType{$2}; VARDTYPE(dtp); }
        |       varParamReset yTYPE__ETC forward_type
                        { /*VARRESET-in-varParam*/
                          AstNodeDType* const dtp = new AstParseTypeDType{$2, $3}; VARDTYPE(dtp); }
        |       yTYPE__ETC
                        { /*VARRESET-in-varParam*/
                          AstNodeDType* const dtp = new AstParseTypeDType{$1}; VARDTYPE(dtp); }
        |       yTYPE__ETC forward_type
                        { /*VARRESET-in-varParam*/
                          AstNodeDType* const dtp = new AstParseTypeDType{$1, $2}; VARDTYPE(dtp); }
        ;

forward_type:  // ==IEEE: forward_type
                yENUM                                   { $$ = VFwdType::ENUM; }
        |       ySTRUCT                                 { $$ = VFwdType::STRUCT; }
        |       yUNION                                  { $$ = VFwdType::UNION; }
        |       yCLASS                                  { $$ = VFwdType::CLASS; }
        |       yINTERFACE yCLASS                       { $$ = VFwdType::INTERFACE_CLASS; }
        ;

net_declaration:         // IEEE: net_declaration - excluding implict
                net_declarationFront netSigList ';'
                        { $$ = $2;
                          if (GRAMMARP->m_netStrengthp) {
                              VL_DO_CLEAR(delete GRAMMARP->m_netStrengthp, GRAMMARP->m_netStrengthp = nullptr);
                          }
                          GRAMMARP->setNetDelay(nullptr); }
        ;

net_declarationFront:           // IEEE: beginning of net_declaration
                net_declRESET net_type driveStrengthE net_scalaredE net_dataTypeE
                        { VARDTYPE_NDECL($5);
                          GRAMMARP->setNetStrength($3); }
        |       net_declRESET yINTERCONNECT signingE rangeListE
                        { BBUNSUP($<fl>2, "Unsupported: interconnect");
                          VARDECL(WIRE);
                          AstNodeDType* const dtp = GRAMMARP->addRange(
                                    new AstBasicDType{$2, LOGIC_IMPLICIT, $3}, $4, true);
                          VARDTYPE_NDECL(dtp); }
        ;

net_declRESET:
                /* empty */                             { VARRESET_NONLIST(UNKNOWN); }
        ;

net_scalaredE:
                /* empty */                             { }
        //                      //UNSUP: ySCALARED/yVECTORED ignored
        |       ySCALARED                               { }
        |       yVECTORED                               { }
        ;

net_dataTypeE:
        //                      // If there's a SV data type there shouldn't be a delay on this wire
        //                      // Otherwise #(...) can't be determined to be a delay or parameters
        //                      // Submit this as a footnote to the committee
                var_data_type                           { $$ = $1; }
        |       signingE rangeList delay_controlE
                        { $$ = GRAMMARP->addRange(new AstBasicDType{$2->fileline(), LOGIC, $1},
                                                                    $2, true);
                          GRAMMARP->setNetDelay($3); }  // not implicit
        |       signing
                        { $$ = new AstBasicDType{$<fl>1, LOGIC, $1}; }  // not implicit
        |       /*implicit*/ delay_controlE
                        { $$ = new AstBasicDType{CRELINE(), LOGIC};
                          GRAMMARP->setNetDelay($1); }  // not implicit
        ;

net_type:                       // ==IEEE: net_type
                ySUPPLY0                                { VARDECL(SUPPLY0); }
        |       ySUPPLY1                                { VARDECL(SUPPLY1); }
        |       yTRI                                    { VARDECL(TRIWIRE); }
        |       yTRI0                                   { VARDECL(TRI0); }
        |       yTRI1                                   { VARDECL(TRI1); }
        |       yTRIAND                                 { VARDECL(TRIAND); }
        |       yTRIOR                                  { VARDECL(TRIOR); }
        |       yTRIREG                                 { VARDECL(WIRE); BBUNSUP($1, "Unsupported: trireg"); }
        |       yWAND                                   { VARDECL(TRIAND); }
        |       yWIRE                                   { VARDECL(WIRE); }
        |       yWOR                                    { VARDECL(TRIOR); }
        //                      // VAMS - somewhat hackish
        |       yWREAL                                  { VARDECL(WREAL); }
        ;

varParamReset:
                yPARAMETER                              { VARRESET_NONLIST(GPARAM); }
        |       yLOCALPARAM                             { VARRESET_NONLIST(LPARAM); }
        // Note that the type of these params could be modified later according to context (see V3LinkParse)
        ;

port_direction:                 // ==IEEE: port_direction + tf_port_direction
        //                      // IEEE 19.8 just "input" FIRST forces type to wire - we'll ignore that here
        //                      // Only used for ANSI declarations
                yINPUT                                  { VARIO(INPUT); }
        |       yOUTPUT                                 { VARIO(OUTPUT); }
        |       yINOUT                                  { VARIO(INOUT); }
        |       yREF                                    { VARIO(REF); }
        //                      // IEEE 1800-2023: Added 'ref static' and 'const ref static'
        |       yREF ySTATIC__ETC                       { VARIO(REF);
                                                          BBUNSUP($1, "Unsupported: 'ref static' ports"); }
        |       yCONST__REF yREF                        { VARIO(CONSTREF); }
        |       yCONST__REF yREF ySTATIC__ETC           { VARIO(CONSTREF);
                                                          BBUNSUP($1, "Unsupported: 'ref static' ports"); }
        ;

port_directionReset:            // IEEE: port_direction that starts a port_declaraiton
        //                      // Used only for declarations outside the port list
                yINPUT                                  { VARRESET_NONLIST(UNKNOWN); VARIO(INPUT); }
        |       yOUTPUT                                 { VARRESET_NONLIST(UNKNOWN); VARIO(OUTPUT); }
        |       yINOUT                                  { VARRESET_NONLIST(UNKNOWN); VARIO(INOUT); }
        |       yREF                                    { VARRESET_NONLIST(UNKNOWN); VARIO(REF); }
        |       yCONST__REF yREF                        { VARRESET_NONLIST(UNKNOWN); VARIO(CONSTREF); }
        ;

port_declaration:        // ==IEEE: port_declaration
        //                      // Non-ANSI; used inside block followed by ';'
        //                      // SEE ALSO port, tf_port_declaration, data_declarationVarFront
        //
        //                      // IEEE: inout_declaration
        //                      // IEEE: input_declaration
        //                      // IEEE: output_declaration
        //                      // IEEE: ref_declaration
                port_directionReset port_declNetE data_type
        /*mid*/         { VARDTYPE($3); }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $5; }
        |       port_directionReset port_declNetE yVAR data_type
        /*mid*/         { VARDTYPE($4); }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $6; }
        |       port_directionReset port_declNetE yVAR implicit_typeE
        /*mid*/         { VARDTYPE($4); }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $6; }
        |       port_directionReset port_declNetE signingE rangeList
        /*mid*/         { AstNodeDType* const dtp = GRAMMARP->addRange(
                              new AstBasicDType{$4->fileline(), LOGIC_IMPLICIT, $3}, $4, true);
                          VARDTYPE_NDECL(dtp); }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $6; }
        |       port_directionReset port_declNetE signing
        /*mid*/         { AstNodeDType* const dtp = new AstBasicDType{$<fl>3, LOGIC_IMPLICIT, $3};
                          VARDTYPE_NDECL(dtp); }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $5; }
        |       port_directionReset port_declNetE /*implicit*/
        /*mid*/         { VARDTYPE_NDECL(nullptr); /*default_nettype*/ }
        /*cont*/    list_of_variable_decl_assignments                   { $$ = $4; }
        //
        //                      // IEEE: interface_port_declaration
        //                      // IEEE: interface_identifier list_of_interface_identifiers
        //
        //                      // Identical to variable_declaration, resolve in V3LinkDot when id known
        //                      // NO:  id/*interface*/  mpInstnameList
        //
        //                      // IEEE: interface_port_declaration
        //                      // IEEE: interface_identifier '.' modport_identifier list_of_interface_identifiers
        |       id/*interface*/ '.' idAny/*modport*/
        /*mid*/         { VARRESET_NONLIST(VVarType::IFACEREF);
                          AstIfaceRefDType* const dtp = new AstIfaceRefDType{$<fl>1, $<fl>3, "", *$1, *$3};
                          dtp->isPortDecl(true);
                          VARDTYPE(dtp); }
        /*cont*/    mpInstnameList
                        { $$ = VARDONEP($5, nullptr, nullptr); DEL($5); }
        //UNSUP: strengthSpecE for udp_instantiations
        ;

tf_port_declaration:     // ==IEEE: tf_port_declaration
        //                      // Used inside function; followed by ';'
        //                      // SEE ALSO port_declaration, port, data_declarationVarFront
        //
                port_directionReset      data_type      { VARDTYPE($2); }  list_of_tf_variable_identifiers ';'
                        { $$ = $4; }
        |       port_directionReset      implicit_typeE { VARDTYPE_NDECL($2); }  list_of_tf_variable_identifiers ';'
                        { $$ = $4; }
        |       port_directionReset yVAR data_type      { VARDTYPE($3); }  list_of_tf_variable_identifiers ';'
                        { $$ = $5; }
        |       port_directionReset yVAR implicit_typeE { VARDTYPE($3); }  list_of_tf_variable_identifiers ';'
                        { $$ = $5; }
        ;

integer_atom_type: // ==IEEE: integer_atom_type
                yBYTE                                   { $$ = new AstBasicDType{$1, VBasicDTypeKwd::BYTE}; }
        |       ySHORTINT                               { $$ = new AstBasicDType{$1, VBasicDTypeKwd::SHORTINT}; }
        |       yINT                                    { $$ = new AstBasicDType{$1, VBasicDTypeKwd::INT}; }
        |       yLONGINT                                { $$ = new AstBasicDType{$1, VBasicDTypeKwd::LONGINT}; }
        |       yINTEGER                                { $$ = new AstBasicDType{$1, VBasicDTypeKwd::INTEGER}; }
        |       yTIME                                   { $$ = new AstBasicDType{$1, VBasicDTypeKwd::TIME}; }
        ;

integer_vector_type:       // ==IEEE: integer_atom_type
                yBIT                                    { $$ = new AstBasicDType{$1, VBasicDTypeKwd::BIT}; }
        |       yLOGIC                                  { $$ = new AstBasicDType{$1, VBasicDTypeKwd::LOGIC}; }
        |       yREG                                    { $$ = new AstBasicDType{$1, VBasicDTypeKwd::LOGIC}; } // logic==reg
        ;

non_integer_type:  // ==IEEE: non_integer_type
                yREAL                                   { $$ = new AstBasicDType{$1, VBasicDTypeKwd::DOUBLE}; }
        |       yREALTIME                               { $$ = new AstBasicDType{$1, VBasicDTypeKwd::DOUBLE}; }
        |       ySHORTREAL                              { $$ = new AstBasicDType{$1, VBasicDTypeKwd::DOUBLE}; UNSUPREAL($1); }
        ;

signingE:            // IEEE: signing - plus empty
                /*empty*/                               { $$ = VSigning::NOSIGN; }
        |       signing                                 { $$ = $1; }
        ;

signing:             // ==IEEE: signing
                ySIGNED                                 { $<fl>$ = $<fl>1; $$ = VSigning::SIGNED; }
        |       yUNSIGNED                               { $<fl>$ = $<fl>1; $$ = VSigning::UNSIGNED; }
        ;

//************************************************
// Data Types

simple_typeNoRef:   // IEEE: simple_type without idType
        //                      // IEEE: integer_type
                integer_atom_type                       { $$ = $1; }
        |       integer_vector_type                     { $$ = $1; }
        |       non_integer_type                        { $$ = $1; }
        //
        //                      // { generate_block_identifer ... } '.'
        //                      // Need to determine if generate_block_identifier can be lex-detected
        ;

data_type:          // ==IEEE: data_type
        //                      // IEEE: data_type_or_incomplete_class_scoped_type parses same as this
        //                      // as can't tell them apart until link
        //                      // This expansion also replicated elsewhere, IE data_type__AndID
                data_typeNoRef                          { $$ = $1; }
        //
        //                      // REFERENCES
        //
        //                      // IEEE: [ class_scope | package_scope ] type_identifier { packed_dimension }
        //                      // IEEE: class_type
        //                      // IEEE: ps_covergroup_identifier
        //                      // Don't distinguish between types and classes so all these combined
        |       packageClassScopeE idType packed_dimensionListE
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, nullptr};
                          $$ = GRAMMARP->createArray(refp, $3, true); }
        |       packageClassScopeE idType parameter_value_assignmentClass packed_dimensionListE
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, $3};
                          $$ = GRAMMARP->createArray(refp, $4, true); }
        ;

data_typeAny:       // ==IEEE: data_type (accepting idAny)
        //                      // IEEE: data_type_or_incomplete_class_scoped_type parses same as this
        //                      // as can't tell them apart until link
        //                      // This expansion also replicated elsewhere, IE data_type__AndID
                data_typeNoRef                          { $$ = $1; }
        //
        //                      // REFERENCES
        //
        //                      // IEEE: [ class_scope | package_scope ] type_identifier { packed_dimension }
        //                      // IEEE: class_type
        //                      // IEEE: ps_covergroup_identifier
        //                      // Don't distinguish between types and classes so all these combined
        |       packageClassScopeE idAny packed_dimensionListE
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, nullptr};
                          $$ = GRAMMARP->createArray(refp, $3, true); }
        |       packageClassScopeE idAny parameter_value_assignmentClass packed_dimensionListE
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, $3};
                          $$ = GRAMMARP->createArray(refp, $4, true); }
        ;

data_typeBasic:             // IEEE: part of data_type
                integer_vector_type signingE rangeListE { $1->setSignedState($2); $$ = GRAMMARP->addRange($1, $3, true); }
        |       integer_atom_type signingE              { $1->setSignedState($2); $$ = $1; }
        |       non_integer_type                        { $$ = $1; }
        ;

data_typeNoRef:             // ==IEEE: data_type, excluding class_type etc references
                data_typeBasic                          { $$ = $1; }
        |       struct_unionDecl packed_dimensionListE
                        { $$ = GRAMMARP->createArray(
                                   new AstDefImplicitDType{$1->fileline(),
                                                           "__typeimpsu" + cvtToStr(GRAMMARP->s_typeImpNum++),
                                                           VFlagChildDType{}, $1}, $2, true); }
        |       enumDecl packed_dimensionListE
                        { $$ = GRAMMARP->createArray(
                                   new AstDefImplicitDType{$1->fileline(),
                                                           "__typeimpenum" + cvtToStr(GRAMMARP->s_typeImpNum++),
                                                           VFlagChildDType{}, $1}, $2, true); }
        |       ySTRING
                        { $$ = new AstBasicDType{$1, VBasicDTypeKwd::STRING}; }
        |       yCHANDLE
                        { $$ = new AstBasicDType{$1, VBasicDTypeKwd::CHANDLE}; }
        |       yEVENT
                        { $$ = new AstBasicDType{$1, VBasicDTypeKwd::EVENT}; v3Global.setHasEvents(); }
        |       type_referenceDecl                      { $$ = $1; }
        //                      // IEEE: class_scope: see data_type above
        //                      // IEEE: class_type: see data_type above
        //                      // IEEE: ps_covergroup: see data_type above
        //                      // Rules overlap virtual_interface_declaration
        |       yVIRTUAL__INTERFACE yINTERFACE data_typeVirtual
                        { $$ = $3; }
        |       yVIRTUAL__anyID                data_typeVirtual
                        { $$ = $2; }
        ;

data_typeVirtual:           // ==IEEE: data_type after yVIRTUAL [ yINTERFACE ]
        //                      // Parameters here are SV2009
                idAny/*interface*/
                        { AstIfaceRefDType* const ifrefp = new AstIfaceRefDType{$<fl>1, "", *$1};
                          ifrefp->isVirtual(true);
                          $$ = ifrefp; }
        |       idAny/*interface*/ '.' idAny/*modport*/
                        { AstIfaceRefDType* const ifrefp = new AstIfaceRefDType{$<fl>1, $<fl>3, "", *$1, *$3};
                          ifrefp->isVirtual(true);
                          $$ = ifrefp; }
        |       idAny/*interface*/ parameter_value_assignmentClass
                        { AstIfaceRefDType* const ifrefp = new AstIfaceRefDType{$<fl>1, nullptr, "", *$1, "", $2};
                          ifrefp->isVirtual(true);
                          $$ = ifrefp; }
        |       idAny/*interface*/ parameter_value_assignmentClass '.' idAny/*modport*/
                        { AstIfaceRefDType* const ifrefp = new AstIfaceRefDType{$<fl>1, $<fl>4, "", *$1, *$4, $2};
                          ifrefp->isVirtual(true);
                          $$ = ifrefp; }
        ;

data_type_or_void:  // ==IEEE: data_type_or_void
                data_typeAny                            { $$ = $1; }
        |       yVOID
                        { $$ = new AstBasicDType{$1, LOGIC_IMPLICIT};
                          BBUNSUP($1, "Unsupported: void (for tagged unions)"); }
        ;

var_data_type:              // ==IEEE: var_data_type
                data_type                               { $$ = $1; }
        |       yVAR data_type                          { $$ = $2; }
        |       yVAR implicit_typeE                     { $$ = $2; }
        ;

type_referenceBoth:          // IEEE: type_reference
                yTYPE__ETC '(' exprOrDataType ')'
                        { $$ = new AstAttrOf{$1, VAttrType::TYPEID, $3}; }
        ;

type_referenceDecl:         // IEEE: type_reference (as a data type for declaration)
                yTYPE__ETC '(' exprOrDataType ')'
                        { $$ = new AstRefDType{$1, AstRefDType::FlagTypeOfExpr{}, $3}; }
        ;

type_referenceEq:            // IEEE: type_reference (as an ==/!== expression)
                yTYPE__EQ '(' exprOrDataType ')'
                        { $$ = new AstAttrOf{$1, VAttrType::TYPEID, $3}; }
        ;

struct_unionDecl:  // IEEE: part of data_type
        //                      // packedSigningE is NOP for unpacked
                ySTRUCT        packedSigningE '{'
        /*mid*/         { $<nodeUOrStructDTypep>$ = new AstStructDType{$1, $2}; }
        /*cont*/    struct_union_memberListEnd
                        { $$ = $<nodeUOrStructDTypep>4; $$->addMembersp($5); }
        |       yUNION taggedSoftE packedSigningE '{'
        /*mid*/         { $<nodeUOrStructDTypep>$ = new AstUnionDType{$1, $2, $3}; }
        /*cont*/    struct_union_memberListEnd
                        { $$ = $<nodeUOrStructDTypep>5; $$->addMembersp($6); }
        ;

struct_union_memberListEnd: // IEEE: { struct_union_member } '}'
                struct_union_memberList '}'                     { $$ = $1; }
        //
        |       struct_union_memberList error '}'               { $$ = $1; }  // LCOV_EXCL_LINE
        |       error '}'                                       { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

struct_union_memberList: // IEEE: { struct_union_member }
                struct_union_member                             { $$ = $1; }

        |       struct_union_memberList struct_union_member     { $$ = addNextNull($1, $2); }
        //
        |       struct_union_memberList error ';'               { $$ = $1; }  // LCOV_EXCL_LINE
        |       error ';'                                       { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

struct_union_member:     // ==IEEE: struct_union_member
        //                      // UNSUP random_qualifer not propagated until have randomize support
                random_qualifierE data_type_or_void
        /*mid*/         { GRAMMARP->m_memDTypep = $2; }  // As a list follows, need to attach this dtype to each member.
        /*cont*/    list_of_member_decl_assignments ';'
                        { $$ = $4; DEL(GRAMMARP->m_memDTypep); GRAMMARP->m_memDTypep = nullptr; }
        |       vlTag                                   { $$ = nullptr; }
        ;

list_of_member_decl_assignments: // Derived from IEEE: list_of_variable_decl_assignments
                member_decl_assignment                  { $$ = $1; }
        |       list_of_member_decl_assignments ',' member_decl_assignment      { $$ = addNextNull($1, $3); }
        ;

member_decl_assignment:   // Derived from IEEE: variable_decl_assignment
        //                      // At present we allow only packed structures/unions.
        //                      // So this is different from variable_decl_assignment
                idAny variable_dimensionListE
                        { $$ = new AstMemberDType{$<fl>1, *$1, VFlagChildDType{},
                                                  GRAMMARP->createArray((GRAMMARP->m_memDTypep
                                                                         ? GRAMMARP->m_memDTypep->cloneTree(true) : nullptr),
                                                                        $2, false),
                                                  nullptr};
                          PARSEP->tagNodep($$);
                        }
        |       idAny variable_dimensionListE '=' variable_declExpr
                        { $$ = new AstMemberDType{$<fl>1, *$1, VFlagChildDType{},
                                                  GRAMMARP->createArray((GRAMMARP->m_memDTypep
                                                                         ? GRAMMARP->m_memDTypep->cloneTree(true) : nullptr),
                                                                        $2, false),
                                                  $4};
                          PARSEP->tagNodep($$);
                        }
        |       idSVKwd                                 { $$ = nullptr; }
        //
        //                      // IEEE: "dynamic_array_variable_identifier '[' ']' [ '=' dynamic_array_new ]"
        //                      // Matches above with variable_dimensionE = "[]"
        //                      // IEEE: "class_variable_identifier [ '=' class_new ]"
        //                      // variable_dimensionE must be empty
        //                      // Pushed into variable_declExpr:dynamic_array_new
        ;

list_of_variable_decl_assignments:        // ==IEEE: list_of_variable_decl_assignments
                variable_decl_assignment                { $$ = $1; }
        |       list_of_variable_decl_assignments ',' variable_decl_assignment  { $$ = addNextNull($1, $3); }
        ;

variable_decl_assignment: // ==IEEE: variable_decl_assignment
                id variable_dimensionListE sigAttrListE
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3); }
        |       id variable_dimensionListE sigAttrListE '=' variable_declExpr
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3); $$->valuep($5); }
        |       idSVKwd                                 { $$ = nullptr; }
        //
        //                      // IEEE: "dynamic_array_variable_identifier '[' ']' [ '=' dynamic_array_new ]"
        |       id variable_dimensionListE sigAttrListE yP_EQ__NEW dynamic_array_new
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3); $$->valuep($5); }
        //                      // IEEE: "class_variable_identifier [ '=' class_new ]"
        //                      // variable_dimensionE must be empty
        |       id variable_dimensionListE sigAttrListE yP_EQ__NEW class_new
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3); $$->valuep($5); }
        ;

list_of_tf_variable_identifiers: // ==IEEE: list_of_tf_variable_identifiers
                tf_variable_identifier                  { $$ = $1; }
        |       list_of_tf_variable_identifiers ',' tf_variable_identifier      { $$ = $1->addNext($3); }
        ;

tf_variable_identifier:           // IEEE: part of list_of_tf_variable_identifiers
                id variable_dimensionListE sigAttrListE exprEqE
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3);
                          if ($4) AstNode::addNext<AstNode, AstNode>(
                                      $$, new AstAssign{$4->fileline(), new AstParseRef{$<fl>1, *$1}, $4}); }
        ;

variable_declExpr:               // IEEE: part of variable_decl_assignment - rhs of expr
                expr                                    { $$ = $1; }
        |       dynamic_array_new                       { $$ = $1; }
        |       class_newNoScope                        { $$ = $1; }
        ;

variable_dimensionListE:    // IEEE: variable_dimension + empty
                /*empty*/                               { $$ = nullptr; }
        |       variable_dimensionList                  { $$ = $1; }
        ;

variable_dimensionList:     // IEEE: variable_dimension + empty
                variable_dimension                      { $$ = $1; }
        |       variable_dimensionList variable_dimension       { $$ = $1->addNext($2); }
        ;

variable_dimension: // ==IEEE: variable_dimension
        //                      // IEEE: unsized_dimension
                '[' ']'                                 { $$ = new AstUnsizedRange{$1}; }
        //                      // IEEE: unpacked_dimension
        |       anyrange                                { $$ = $1; }
        //                      // IEEE: unpacked_dimension (if const_expr)
        //                      // IEEE: associative_dimension (if data_type)
        //                      // Can't tell which until see if expr is data type or not
        |       '[' exprOrDataType ']'                  { $$ = new AstBracketRange{$1, $2}; }
        |       yP_BRASTAR ']'                          { $$ = new AstWildcardRange{$1}; }
        |       '[' '*' ']'                             { $$ = new AstWildcardRange{$1}; }
        //                      // IEEE: queue_dimension
        //                      // '[' '$' ']' -- $ is part of expr, see '[' constExpr ']'
        //                      // '[' '$' ':' expr ']' -- anyrange:expr:$
        ;

random_qualifierE:  // IEEE: random_qualifier + empty
                /*empty*/                               { $$ = VMemberQualifiers::none(); }
        |       random_qualifier                        { $$ = $1; }
        ;

random_qualifier:   // ==IEEE: random_qualifier
                yRAND                                   { $$ = VMemberQualifiers::none(); $$.m_rand = true; }
        |       yRANDC                                  { $$ = VMemberQualifiers::none(); $$.m_randc = true; }
        ;

taggedSoftE:
                /*empty*/                               { $$ = false; }
        |       ySOFT                                   { $$ = true; }
        |       yTAGGED                                 { $$ = false; BBUNSUP($<fl>1, "Unsupported: tagged union"); }
        ;

packedSigningE:
        //                      // VSigning::NOSIGN overloaded to indicate not packed
                /*empty*/                               { $$ = VSigning::NOSIGN; }
        |       yPACKED signingE                        { $$ = $2; if ($$ == VSigning::NOSIGN) $$ = VSigning::UNSIGNED; }
        ;

//************************************************
// enum

// IEEE: part of data_type
enumDecl:
                yENUM enum_base_typeE '{' enum_nameList '}'
                        { $$ = new AstEnumDType{$1, VFlagChildDType{}, $2, $4}; }
        ;

enum_base_typeE:    // IEEE: enum_base_type
                /* empty */
                        { $$ = new AstBasicDType{CRELINE(), VBasicDTypeKwd::INT}; }
        //                      // Not in spec, but obviously "enum [1:0]" should work
        //                      // implicit_type expanded, without empty
        //                      // Note enum base types are always packed data types
        |       signingE rangeList
                        { $$ = GRAMMARP->addRange(new AstBasicDType{$2->fileline(), LOGIC_IMPLICIT, $1}, $2, true); }
        |       signing
                        { $$ = new AstBasicDType{$<fl>1, LOGIC_IMPLICIT, $1}; }
        //
        |       integer_atom_type signingE
                        { $1->setSignedState($2); $$ = $1; }
        |       integer_vector_type signingE rangeListE
                        { $1->setSignedState($2); $$ = GRAMMARP->addRange($1, $3, true); }
        //                      // below can be idAny or yaID__aTYPE
        //                      // IEEE requires a type, though no shift conflict if idAny
        //                      // IEEE: type_identifier [ packed_dimension ]
        //                      // however other simulators allow [ class_scope | package_scope ] type_identifier
        |       idAny rangeListE
                        { $$ = GRAMMARP->createArray(new AstRefDType{$<fl>1, *$1}, $2, true); }
        |       packageClassScope idAny rangeListE
                        { AstRefDType* refp = new AstRefDType{$<fl>2, *$2, $1, nullptr};
                          $$ = GRAMMARP->createArray(refp, $3, true); }
        ;

enum_nameList:
                enum_name_declaration                   { $$ = $1; }
        |       enum_nameList ',' enum_name_declaration { $$ = addNextNull($1, $3); }
        ;

enum_name_declaration:   // ==IEEE: enum_name_declaration
                idAny/*enum_identifier*/ enumNameRangeE enumNameStartE
                        { $$ = new AstEnumItem{$<fl>1, *$1, $2, $3}; }
        ;

enumNameRangeE:          // IEEE: second part of enum_name_declaration
                /* empty */
                        { $$ = nullptr; }
        |       '[' intnumAsConst ']'
                        { $$ = new AstRange{$1, new AstConst{$1, 0}, new AstConst($1, $2->toSInt() - 1)}; DEL($2); }
        |       '[' intnumAsConst ':' intnumAsConst ']'
                        { $$ = new AstRange{$1, $2, $4}; }
        ;

enumNameStartE:      // IEEE: third part of enum_name_declaration
                /* empty */                             { $$ = nullptr; }
        |       '=' constExpr                           { $$ = $2; }
        ;

intnumAsConst:
                yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }
        ;

//************************************************
// Typedef

data_declaration:        // ==IEEE: data_declaration
        //                      // VARRESET can't be called here - conflicts
                data_declarationVar                     { $$ = $1; }
        |       type_declaration                        { $$ = $1; }
        |       package_import_declaration              { $$ = $1; }
        //                      // IEEE: virtual_interface_declaration
        //                      // "yVIRTUAL yID yID" looks just like a data_declaration
        //                      // Therefore the virtual_interface_declaration term isn't used
        //                      // 1800-2009:
        |       nettype_declaration                     { $$ = $1; }
        |       vlTag                                   { $$ = nullptr; }
        ;

class_property:          // ==IEEE: class_property, which is {property_qualifier} data_declaration
                memberQualListE data_declarationVarClass
                        { $$ = $2; $1.applyToNodes($2); }
        |       memberQualListE type_declaration
                        { $$ = $2; if (VN_IS($2, Typedef)) $1.applyToNodes(VN_AS($2, Typedef)); }
        //                      // UNSUP: Import needs to apply local/protected from memberQualList, and error on others
        |       memberQualListE package_import_declaration
                        { $$ = $2; }
        //                      // IEEE: virtual_interface_declaration
        //                      // "yVIRTUAL yID yID" looks just like a data_declaration
        //                      // Therefore the virtual_interface_declaration term isn't used
        ;

data_declarationVar:      // IEEE: part of data_declaration
        //                      // The first declaration has complications between assuming what's
        //                      // the type vs ID declaring
                data_declarationVarFront list_of_variable_decl_assignments ';'  { $$ = $2; }
        ;

data_declarationVarClass: // IEEE: part of data_declaration (for class_property)
        //                      // The first declaration has complications between assuming what's
        //                      // the type vs ID declaring
                data_declarationVarFrontClass list_of_variable_decl_assignments ';'     { $$ = $2; }
        ;

data_declarationVarFront:       // IEEE: part of data_declaration
        //                      // Non-ANSI; used inside block followed by ';'
        //                      // SEE ALSO port_declaration, tf_port_declaration, port
        //
        //                      // Expanded: "constE yVAR lifetimeE data_type"
        //                      // implicit_type expanded into /*empty*/ or "signingE rangeList"
                yVAR lifetimeE data_type
                        { VARRESET_NONLIST(VAR); VARLIFE($2); VARDTYPE($3); }
        |       yVAR lifetimeE
                        { VARRESET_NONLIST(VAR); VARLIFE($2);
                          AstNodeDType* const dtp = new AstBasicDType{$<fl>1, LOGIC_IMPLICIT};
                          VARDTYPE(dtp); }
        |       yVAR lifetimeE signingE rangeList
                        { /*VARRESET-in-ddVar*/ VARLIFE($2);
                          AstNodeDType* const dtp = GRAMMARP->addRange(
                              new AstBasicDType{$<fl>1, LOGIC_IMPLICIT, $3}, $4, true);
                          VARDTYPE(dtp); }
        //
        //                      // implicit_type expanded into /*empty*/ or "signingE rangeList"
        |       yCONST__ETC yVAR lifetimeE data_type
                        { VARRESET_NONLIST(VAR); VARLIFE($3);
                          AstNodeDType* const dtp = new AstConstDType{$<fl>2, VFlagChildDType{}, $4};
                          VARDTYPE(dtp); }
        |       yCONST__ETC yVAR lifetimeE
                        { VARRESET_NONLIST(VAR); VARLIFE($3);
                          AstNodeDType* const dtp = new AstConstDType{$<fl>2, VFlagChildDType{},
                                                          new AstBasicDType{$<fl>2, LOGIC_IMPLICIT}};
                          VARDTYPE(dtp); }
        |       yCONST__ETC yVAR lifetimeE signingE rangeList
                        { VARRESET_NONLIST(VAR); VARLIFE($3);
                          AstNodeDType* const dtp = new AstConstDType{$<fl>2, VFlagChildDType{},
                                  GRAMMARP->addRange(new AstBasicDType{$<fl>2, LOGIC_IMPLICIT, $4}, $5, true)};
                          VARDTYPE(dtp); }
        //
        //                      // Expanded: "constE lifetimeE data_type"
        |       /**/                  data_type
                        { VARRESET_NONLIST(VAR); VARDTYPE($1); }
        |       /**/        lifetime  data_type
                        { VARRESET_NONLIST(VAR); VARLIFE($1); VARDTYPE($2); }
        |       yCONST__ETC lifetimeE data_type
                        { VARRESET_NONLIST(VAR); VARLIFE($2);
                          AstNodeDType* const dtp = new AstConstDType{$<fl>1, VFlagChildDType{}, $3};
                          VARDTYPE(dtp); }
        //                      // = class_new is in variable_decl_assignment
        ;

data_declarationVarFrontClass:  // IEEE: part of data_declaration (for class_property)
        //                      // VARRESET called before this rule
        //                      // yCONST is removed, added to memberQual rules
        //                      // implicit_type expanded into /*empty*/ or "signingE rangeList"
                yVAR lifetimeE data_type        { VARRESET_NONLIST(VAR); VARLIFE($2); VARDTYPE($3); }
        |       yVAR lifetimeE                  { VARRESET_NONLIST(VAR); VARLIFE($2); }
        |       yVAR lifetimeE signingE rangeList
                        { /*VARRESET-in-ddVar*/
                          AstNodeDType* const dtp = GRAMMARP->addRange(new AstBasicDType{$<fl>1, LOGIC_IMPLICIT, $3}, $4, true);
                          VARDTYPE(dtp);
                          VARLIFE($2); }
        //
        //                      // Expanded: "constE lifetimeE data_type"
        |       data_type                       { VARRESET_NONLIST(VAR); VARDTYPE($1); }
        //                      // lifetime is removed, added to memberQual rules to avoid conflict
        //                      // yCONST is removed, added to memberQual rules to avoid conflict
        //                      // = class_new is in variable_decl_assignment
        ;

nettype_declaration:  // IEEE: nettype_declaration/net_type_declaration
        //                      // Union of data_typeAny and nettype_identifier matching
                yNETTYPE data_typeNoRef
        /*cont*/   idAny/*nettype_identifier*/ ';'
                        { $$ = GRAMMARP->createNettype($<fl>3, *$3); BBUNSUP($<fl>1, "Unsupported: nettype"); }
        |       yNETTYPE data_typeNoRef
        /*cont*/   idAny/*nettype_identifier*/
        /*cont*/   yWITH__ETC packageClassScopeE id/*tf_identifier*/ ';'
                        { $$ = GRAMMARP->createNettype($<fl>3, *$3); BBUNSUP($<fl>1, "Unsupported: nettype with"); }
        |       yNETTYPE packageClassScopeE idAny packed_dimensionListE
        /*cont*/   idAny/*nettype_identifier*/ ';'
                        { $$ = GRAMMARP->createNettype($<fl>5, *$5); BBUNSUP($<fl>1, "Unsupported: nettype"); }
        |       yNETTYPE packageClassScopeE idAny packed_dimensionListE
        /*cont*/   idAny/*nettype_identifier*/
        /*cont*/   yWITH__ETC packageClassScopeE id/*tf_identifier*/ ';'
                        { $$ = GRAMMARP->createNettype($<fl>5, *$5); BBUNSUP($<fl>1, "Unsupported: nettype with"); }
        |       yNETTYPE packageClassScopeE idAny parameter_value_assignmentClass packed_dimensionListE
        /*cont*/   idAny/*nettype_identifier*/ ';'
                        { $$ = GRAMMARP->createNettype($<fl>6, *$6); BBUNSUP($<fl>1, "Unsupported: nettype"); }
        |       yNETTYPE packageClassScopeE idAny parameter_value_assignmentClass packed_dimensionListE
        /*cont*/   idAny/*nettype_identifier*/
        /*cont*/   yWITH__ETC packageClassScopeE id/*tf_identifier*/ ';'
                        { $$ = GRAMMARP->createNettype($<fl>6, *$6); BBUNSUP($<fl>1, "Unsupported: nettype with"); }
        ;

implicit_typeE:             // IEEE: part of *data_type_or_implicit
        //                      // Also expanded in data_declaration
                /* empty */
                        { $$ = nullptr; }
        |       signingE rangeList
                        { $$ = GRAMMARP->addRange(new AstBasicDType{$2->fileline(), LOGIC_IMPLICIT, $1}, $2, true); }
        |       signing
                        { $$ = new AstBasicDType{$<fl>1, LOGIC_IMPLICIT, $1}; }
        ;

assertion_variable_declaration:  // IEEE: assertion_variable_declaration
        //                      // IEEE: var_data_type expanded
                var_data_type                        { VARRESET_NONLIST(VAR); VARDTYPE_NDECL($1); }
        /*cont*/    list_of_variable_decl_assignments ';'     { $$ = $3; }
        ;

type_declaration:        // ==IEEE: type_declaration
                                // Data_type expanded
                yTYPEDEF data_typeNoRef
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstNodeDType* const dtp = $2;
                          $$ = GRAMMARP->createTypedef($<fl>3, *$3, $5, dtp, $4); }

        // IEEE 1800-2017 6.18 typedef: dotted or arrayed type identifier
        // Handles interface typedef references like if0.rq_t and if0[0].rq_t (arrays allowed after first component)
        |       yTYPEDEF idDottedOrArrayed
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
              { VARRESET_NONLIST(LPARAM);
                AstParseTypeDType* const ptypep = new AstParseTypeDType{$<fl>2, VFwdType::NONE};
                VARDTYPE(ptypep);
                AstVar* const varp = VARDONEA($<fl>3, *$3, $4, $5);
                // idDottedOrArrayed produces Dot/SelBit tree for hierarchical refs like if0[0].rq_t
                varp->valuep($2);
                $$ = varp; }

        // IEEE 1800-2017 6.18 typedef with hierarchical type identifier
        // Special-case array on first component requiring a '.' after ']' to disambiguate from packed dims
        // Examples: typedef if0[0].rq_t my_t; typedef if0[0].x_if.rq_t my_t;
        |       yTYPEDEF id '[' expr ']' '.' idDottedSelMore
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
              { VARRESET_NONLIST(LPARAM);
                AstParseTypeDType* const ptypep = new AstParseTypeDType{$<fl>2, VFwdType::NONE};
                VARDTYPE(ptypep);
                AstVar* const varp = VARDONEA($<fl>8, *$8, $9, $10);
                AstNodeExpr* const arrp = new AstSelBit{$3, new AstParseRef{$<fl>2, *$2, nullptr, nullptr}, $4};
                varp->valuep(new AstDot{$6, false, arrp, $7});
                $$ = varp; }

        |       yTYPEDEF packageClassScope idAny packed_dimensionListE
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstRefDType* const refp = new AstRefDType{$<fl>3, *$3, $2, nullptr};
                          AstNodeDType* const dtp = GRAMMARP->createArray(refp, $4, true);
                          $$ = GRAMMARP->createTypedef($<fl>5, *$5, $7, dtp, $6); }
        |       yTYPEDEF packageClassScope idAny parameter_value_assignmentClass packed_dimensionListE
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstRefDType* const refp = new AstRefDType{$<fl>3, *$3, $2, $4};
                          AstNodeDType* const dtp = GRAMMARP->createArray(refp, $5, true);
                          $$ = GRAMMARP->createTypedef($<fl>6, *$6, $8, dtp, $7); }

        // Type alias without packed dimensions: typedef existing_t new_t;
        |       yTYPEDEF idAny idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, nullptr, nullptr};
                          $$ = GRAMMARP->createTypedef($<fl>3, *$3, $5, refp, $4); }

        // IEEE 1800-2017 6.18.2 typedef with packed dimensions on an existing type identifier
        // Disambiguated from interface array access by requiring ':' inside the brackets
        // (applies to both plain identifiers and type identifiers)
        |       yTYPEDEF id '[' constExpr ':' constExpr ']' packed_dimensionListE
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, nullptr, nullptr};
                          AstNodeRange* const rangep = new AstRange{$3, $4, $6};
                          AstNodeDType* const dtp = GRAMMARP->createArray(refp, addNextNull(rangep, $8), true);
                          $$ = GRAMMARP->createTypedef($<fl>9, *$9, $11, dtp, $10); }

        // Same as above but for type identifiers (parameter types, etc.)
        |       yTYPEDEF idType '[' constExpr ':' constExpr ']' packed_dimensionListE
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, nullptr, nullptr};
                          AstNodeRange* const rangep = new AstRange{$3, $4, $6};
                          AstNodeDType* const dtp = GRAMMARP->createArray(refp, addNextNull(rangep, $8), true);
                          $$ = GRAMMARP->createTypedef($<fl>9, *$9, $11, dtp, $10); }

        |       yTYPEDEF idAny parameter_value_assignmentClass packed_dimensionListE
        /*cont*/    idAny variable_dimensionListE dtypeAttrListE ';'
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, nullptr, $3};
                          AstNodeDType* const dtp = GRAMMARP->createArray(refp, $4, true);
                          $$ = GRAMMARP->createTypedef($<fl>5, *$5, $7, dtp, $6); }

        //                      // idAny as also allows redeclaring same typedef again
        |       yTYPEDEF idAny ';'                      { $$ = GRAMMARP->createTypedefFwd($<fl>2, *$2, VFwdType::NONE); }
        //                      // IEEE: expanded forward_type to prevent conflict
        |       yTYPEDEF yENUM idAny ';'                { $$ = GRAMMARP->createTypedefFwd($<fl>3, *$3, VFwdType::ENUM); }
        |       yTYPEDEF ySTRUCT idAny ';'              { $$ = GRAMMARP->createTypedefFwd($<fl>3, *$3, VFwdType::STRUCT); }
        |       yTYPEDEF yUNION idAny ';'               { $$ = GRAMMARP->createTypedefFwd($<fl>3, *$3, VFwdType::UNION); }
        |       yTYPEDEF yCLASS idAny ';'               { $$ = GRAMMARP->createTypedefFwd($<fl>3, *$3, VFwdType::CLASS); }
        |       yTYPEDEF yINTERFACE yCLASS idAny ';'    { $$ = GRAMMARP->createTypedefFwd($<fl>4, *$4, VFwdType::INTERFACE_CLASS); }
        //
        |       yTYPEDEF error idAny ';'                { $$ = GRAMMARP->createTypedefFwd($<fl>3, *$3, VFwdType::NONE); }  // LCOV_EXCL_LINE
        ;

dtypeAttrListE:
                /* empty */                             { $$ = nullptr; }
        |       dtypeAttrList                           { $$ = $1; }
        ;

dtypeAttrList:
                dtypeAttr                               { $$ = $1; }
        |       dtypeAttrList dtypeAttr                 { $$ = addNextNull($1, $2); }
        ;

dtypeAttr:
                yVL_PUBLIC                              { $$ = new AstAttrOf{$1, VAttrType::DT_PUBLIC}; }
        ;

vlTag:                          // verilator tag handling
                yVL_TAG                                 { if (PARSEP->tagNodep()) PARSEP->tagNodep()->tag(*$1); }
        ;

//************************************************
// Module Items

module_itemListE:        // IEEE: Part of module_declaration
                /* empty */                             { $$ = nullptr; }
        |       module_itemList                         { $$ = $1; }
        ;

module_itemList:         // IEEE: Part of module_declaration
                module_item                             { $$ = $1; }
        |       module_itemList module_item             { $$ = addNextNull($1, $2); }
        ;

module_item:             // ==IEEE: module_item
                port_declaration ';'                    { $$ = $1; }
        |       non_port_module_item                    { $$ = $1; }
        ;

non_port_module_item:    // ==IEEE: non_port_module_item
                generate_region                         { $$ = $1; }
                                // not in IEEE, but presumed so can do yBEGIN ... yEND
        |       genItemBegin                            { $$ = $1; }
        |       module_or_generate_item                 { $$ = $1; }
        |       specify_block                           { $$ = $1; }
        |       specparam_declaration                   { $$ = $1; }
        |       program_declaration
                        { $$ = nullptr; BBUNSUP(CRELINE(), "Unsupported: program decls within module decls"); }
        |       module_declaration
                        { $$ = nullptr; BBUNSUP(CRELINE(), "Unsupported: module decls within module decls"); }
        |       interface_declaration
                        { $$ = nullptr; BBUNSUP(CRELINE(), "Unsupported: interface decls within module decls"); }
        |       timeunits_declaration                   { $$ = $1; }
        //                      // Verilator specific
        |       vlScBlock                               { $$ = $1; }
        |       yVL_HIER_BLOCK                          { $$ = new AstPragma{$1, VPragmaType::HIER_BLOCK}; }
        |       yVL_INLINE_MODULE                       { $$ = new AstPragma{$1, VPragmaType::INLINE_MODULE}; }
        |       yVL_NO_INLINE_MODULE                    { $$ = new AstPragma{$1, VPragmaType::NO_INLINE_MODULE}; }
        |       yVL_PUBLIC_MODULE                       { $$ = new AstPragma{$1, VPragmaType::PUBLIC_MODULE}; v3Global.dpi(true); }
        ;

vlScBlock:  // Verilator-specific `systemc_* blocks
                yaSCHDR     { $$ = new AstSystemCSection{$<fl>1, VSystemCSectionType::HDR, *$1};  }
        |       yaSCHDRP    { $$ = new AstSystemCSection{$<fl>1, VSystemCSectionType::HDR_POST, *$1}; }
        |       yaSCINT     { $$ = new AstSystemCSection{$<fl>1, VSystemCSectionType::INT, *$1}; }
        |       yaSCIMP     { $$ = new AstSystemCSection{$<fl>1, VSystemCSectionType::IMP, *$1}; }
        |       yaSCIMPH    { $$ = new AstSystemCSection{$<fl>1, VSystemCSectionType::IMP_HDR, *$1}; }
        |       yaSCCTOR    { $$ = new AstSystemCSection{$<fl>1, VSystemCSectionType::CTOR, *$1}; }
        |       yaSCDTOR    { $$ = new AstSystemCSection{$<fl>1, VSystemCSectionType::DTOR, *$1}; }
        ;


module_or_generate_item: // ==IEEE: module_or_generate_item
        //                      // IEEE: parameter_override
                yDEFPARAM list_of_defparam_assignments ';'      { $$ = $2; }
        //                      // IEEE: gate_instantiation + udp_instantiation + module_instantiation
        //                      // not here, see etcInst in module_common_item
        //                      // We joined udp & module definitions, so this goes here
        |       combinational_body                      { $$ = $1; }
        //                      // This module_common_item shared with
        //                      // interface_or_generate_item:module_common_item
        |       module_common_item                      { $$ = $1; }
        ;

module_common_item:      // ==IEEE: module_common_item
                module_or_generate_item_declaration     { $$ = $1; }
        //                      // IEEE: interface_instantiation
        //                      // + IEEE: program_instantiation
        //                      // + module_instantiation from module_or_generate_item
        |       etcInst                                 { $$ = $1; }
        |       assertion_item                          { $$ = $1; }
        |       bind_directive                          { $$ = $1; }
        |       continuous_assign                       { $$ = $1; }
        |       net_alias                               { $$ = $1; }
        |       initial_construct                       { $$ = $1; }
        |       final_construct                         { $$ = $1; }
        |       always_construct                        { $$ = $1; }
        |       loop_generate_construct                 { $$ = $1; }
        |       conditional_generate_construct          { $$ = $1; }
        |       severity_system_task                    { $$ = $1; }
        |       sigAttrScope                            { $$ = nullptr; }
        //
        |       error ';'                               { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

always_construct:        // IEEE: == always_construct
                yALWAYS       stmt                 { $$ = new AstAlways{$1, VAlwaysKwd::ALWAYS, nullptr, $2}; }
        |       yALWAYS_FF    stmt                 { $$ = new AstAlways{$1, VAlwaysKwd::ALWAYS_FF, nullptr, $2}; }
        |       yALWAYS_LATCH stmt                 { $$ = new AstAlways{$1, VAlwaysKwd::ALWAYS_LATCH, nullptr, $2}; }
        |       yALWAYS_COMB  stmt                 { $$ = new AstAlways{$1, VAlwaysKwd::ALWAYS_COMB, nullptr, $2}; }
        ;

continuous_assign:       // IEEE: continuous_assign
                yASSIGN driveStrengthE delay_controlE assignList ';'
                        { $$ = $4;
                          STRENGTH_LIST($4, $2);
                          DELAY_LIST($4, $3); }
        ;

initial_construct:       // IEEE: initial_construct
                yINITIAL stmt                      { $$ = new AstInitial{$1, $2}; }
        ;


net_alias:               // IEEE: net_alias
                yALIAS variable_lvalue aliasEqList ';'
                        { $2->addNext($3);
                          $$ = new AstAlias{$1, $2}; }
        ;

aliasEqList:                    // IEEE: part of net_alias
                '=' variable_lvalue                     { $$ = $2; }
        |       aliasEqList '=' variable_lvalue         { $$ = $1->addNext($3); }
        ;

final_construct:         // IEEE: final_construct
                yFINAL stmt                        { $$ = new AstFinal{$1, $2}; }
        ;

module_or_generate_item_declaration:     // ==IEEE: module_or_generate_item_declaration
                package_or_generate_item_declaration    { $$ = $1; }
        |       genvar_declaration                      { $$ = $1; }
        |       clocking_declaration                    { $$ = $1; }
        |       modDefaultClocking                      { $$ = $1; }
        |       defaultDisable                          { $$ = $1; }
        ;

modDefaultClocking:  // IEEE: part of module_or_generate_item_declaration/checker_or_...
                yDEFAULT yCLOCKING idAny/*new-clocking_identifier*/ ';'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: default clocking identifier"); }
        ;

defaultDisable:  // IEEE: part of module_/checker_or_generate_item_declaration
                yDEFAULT yDISABLE yIFF expr/*expression_or_dist*/ ';'
                        { $$ = new AstDefaultDisable{$1, $4}; }
        ;

bind_directive:          // ==IEEE: bind_directive + bind_target_scope
        //                      // ';' - Note IEEE grammar is wrong, includes extra ';'
        //                      // - it's already in module_instantiation
        //                      // We merged the rules - id may be a bind_target_instance or
        //                      // module_identifier or interface_identifier
                yBIND bind_target_instance bind_instantiation   { $$ = new AstBind{$<fl>2, *$2, $3}; }
        |       yBIND bind_target_instance ':' bind_target_instance_list bind_instantiation
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: Bind with instance list"); DEL($5); }
        ;

bind_target_instance_list:      // ==IEEE: bind_target_instance_list
                bind_target_instance                    { }
        |       bind_target_instance_list ',' bind_target_instance      { }
        ;

bind_target_instance:     // ==IEEE: bind_target_instance
        //UNSUP hierarchical_identifierBit              { }
                idAny                                   { $$ = $1; }
        ;

bind_instantiation:      // ==IEEE: bind_instantiation
        //                      // IEEE: program_instantiation
        //                      // IEEE: + module_instantiation
        //                      // IEEE: + interface_instantiation
        //                      // Need to get an AstBind instead of AstCell, so have special rules
                instDecl                                { $$ = $1; }
        ;

//************************************************
// Generates
//
// Way down in generate_item is speced a difference between module,
// interface and checker generates.  modules and interfaces are almost
// identical (minus DEFPARAMs) so we overlap them.  Checkers are too
// different, so we copy all rules for checkers.

generate_region:         // ==IEEE: generate_region
                yGENERATE genItemList yENDGENERATE   { $$ = $2; }
        |       yGENERATE yENDGENERATE                  { $$ = nullptr; }
        ;

c_generate_region:  // IEEE: generate_region (for checkers)
                                 yGENERATE c_genItemList yENDGENERATE   { $$ = $2; }         |       yGENERATE yENDGENERATE                  { $$ = nullptr; }      // {copied}
        ;

i_generate_region:  // IEEE: generate_region (for interface)
                                 yGENERATE i_genItemList yENDGENERATE   { $$ = $2; }         |       yGENERATE yENDGENERATE                  { $$ = nullptr; }      // {copied}
        ;

generate_block_or_null:  // IEEE: generate_block_or_null (called from gencase/genif/genfor)
        //      ';'             // is included in
        //                      // IEEE: generate_block
        //                      // Must always return a BEGIN node, or nullptr - see GenFor construction
                generate_item
                        { $$ = $1 ? (new AstGenBlock{$1->fileline(), "", $1, true}) : nullptr; }
        |       genItemBegin                         { $$ = $1; }
        ;

c_generate_block_or_null:  // IEEE: generate_block_or_null (for checkers)
                                 c_generate_item                         { $$ = $1 ? (new AstGenBlock{$1->fileline(), "", $1, true}) : nullptr; }         |       c_genItemBegin                         { $$ = $1; }       // {copied}
        ;

genItemBegin:            // IEEE: part of generate_block
                yBEGIN genItemList yEND              { $$ = new AstGenBlock{$1, "", $2, false}; }
        |       yBEGIN yEND                             { $$ = nullptr; }
        |       id yP_COLON__BEGIN yBEGIN genItemList yEND endLabelE
                        { $$ = new AstGenBlock{$<fl>1, *$1, $4, false};
                          GRAMMARP->endLabel($<fl>6, *$1, $6); }
        |       id yP_COLON__BEGIN yBEGIN yEND endLabelE
                        { $$ = new AstGenBlock{$<fl>1, *$1, nullptr, false};
                          GRAMMARP->endLabel($<fl>5, *$1, $5); }
        |       yBEGIN ':' idAny genItemList yEND endLabelE
                        { $$ = new AstGenBlock{$<fl>3, *$3, $4, false};
                          GRAMMARP->endLabel($<fl>6, *$3, $6); }
        |       yBEGIN ':' idAny yEND endLabelE
                        { $$ = new AstGenBlock{$<fl>3, *$3, nullptr, false};
                          GRAMMARP->endLabel($<fl>5, *$3, $5); }
        ;

c_genItemBegin:  // IEEE: part of generate_block (for checkers)
                                 yBEGIN c_genItemList yEND              { $$ = new AstGenBlock{$1, "", $2, false}; }         |       yBEGIN yEND                             { $$ = nullptr; }         |       id yP_COLON__BEGIN yBEGIN c_genItemList yEND endLabelE                         { $$ = new AstGenBlock{$<fl>1, *$1, $4, false};                           GRAMMARP->endLabel($<fl>6, *$1, $6); }         |       id yP_COLON__BEGIN yBEGIN yEND endLabelE                         { $$ = new AstGenBlock{$<fl>1, *$1, nullptr, false};                           GRAMMARP->endLabel($<fl>5, *$1, $5); }         |       yBEGIN ':' idAny c_genItemList yEND endLabelE                         { $$ = new AstGenBlock{$<fl>3, *$3, $4, false};                           GRAMMARP->endLabel($<fl>6, *$3, $6); }         |       yBEGIN ':' idAny yEND endLabelE                         { $$ = new AstGenBlock{$<fl>3, *$3, nullptr, false};                           GRAMMARP->endLabel($<fl>5, *$3, $5); }                 // {copied}
        ;

i_genItemBegin:  // IEEE: part of generate_block (for interfaces)
                                 yBEGIN i_genItemList yEND              { $$ = new AstGenBlock{$1, "", $2, false}; }         |       yBEGIN yEND                             { $$ = nullptr; }         |       id yP_COLON__BEGIN yBEGIN i_genItemList yEND endLabelE                         { $$ = new AstGenBlock{$<fl>1, *$1, $4, false};                           GRAMMARP->endLabel($<fl>6, *$1, $6); }         |       id yP_COLON__BEGIN yBEGIN yEND endLabelE                         { $$ = new AstGenBlock{$<fl>1, *$1, nullptr, false};                           GRAMMARP->endLabel($<fl>5, *$1, $5); }         |       yBEGIN ':' idAny i_genItemList yEND endLabelE                         { $$ = new AstGenBlock{$<fl>3, *$3, $4, false};                           GRAMMARP->endLabel($<fl>6, *$3, $6); }         |       yBEGIN ':' idAny yEND endLabelE                         { $$ = new AstGenBlock{$<fl>3, *$3, nullptr, false};                           GRAMMARP->endLabel($<fl>5, *$3, $5); }                 // {copied}
        ;

genItemOrBegin:          // Not in IEEE, but our begin isn't under generate_item
                generate_item                        { $$ = $1; }
        |       genItemBegin                         { $$ = $1; }
        ;

c_genItemOrBegin:  // (for checkers)
                                 c_generate_item                        { $$ = $1; }         |       c_genItemBegin                         { $$ = $1; }       // {copied}
        ;

i_genItemOrBegin:  // (for interfaces)
                interface_item                          { $$ = $1; }
        |       i_genItemBegin                          { $$ = $1; }
        ;

genItemList:
                genItemOrBegin                       { $$ = $1; }
        |       genItemList genItemOrBegin        { $$ = addNextNull($1, $2); }
        ;

c_genItemList:  // (for checkers)
                                 c_genItemOrBegin                       { $$ = $1; }         |       c_genItemList c_genItemOrBegin        { $$ = addNextNull($1, $2); }          // {copied}
        ;

i_genItemList:  // (for interfaces)
                                 i_genItemOrBegin                       { $$ = $1; }         |       i_genItemList i_genItemOrBegin        { $$ = addNextNull($1, $2); }          // {copied}
        ;

generate_item:           // IEEE: module_or_interface_or_generate_item
        //                      // Only legal when in a generate under a module (or interface under a module)
                module_or_generate_item                 { $$ = $1; }
        //                      // Only legal when in a generate under an interface
        //UNSUP interface_or_generate_item              { $$ = $1; }
        //                      // IEEE: checker_or_generate_item
        //                      // Only legal when in a generate under a checker
        //                      // so below in c_generate_item
        ;

c_generate_item:  // IEEE: generate_item (for checkers)
                checker_or_generate_item                { $$ = $1; }
        ;

conditional_generate_construct:  // ==IEEE: conditional_generate_construct
                yCASE '(' exprTypeCompare ')' case_generate_itemList yENDCASE
                        { $$ = new AstGenCase{$1, $3, $5}; }
        |       yIF '(' exprTypeCompare ')' generate_block_or_null %prec prLOWER_THAN_ELSE
                        { $$ = new AstGenIf{$1, $3, $5, nullptr}; }
        |       yIF '(' exprTypeCompare ')' generate_block_or_null yELSE generate_block_or_null
                        { $$ = new AstGenIf{$1, $3, $5, $7}; }
        ;

c_conditional_generate_construct:  // IEEE: conditional_generate_construct (for checkers)
                                 yCASE '(' exprTypeCompare ')' c_case_generate_itemList yENDCASE                         { $$ = new AstGenCase{$1, $3, $5}; }         |       yIF '(' exprTypeCompare ')' c_generate_block_or_null %prec prLOWER_THAN_ELSE                         { $$ = new AstGenIf{$1, $3, $5, nullptr}; }         |       yIF '(' exprTypeCompare ')' c_generate_block_or_null yELSE c_generate_block_or_null                         { $$ = new AstGenIf{$1, $3, $5, $7}; }       // {copied}
        ;

loop_generate_construct: // ==IEEE: loop_generate_construct
                yFOR '(' genvar_initialization ';' expr ';' genvar_iteration ')' generate_block_or_null
                        { // Convert BEGIN(...) to BEGIN(GENFOR(...)), as we need the BEGIN to hide the local genvar
                          AstGenBlock* lowerp = VN_CAST($9, GenBlock);
                          UASSERT_OBJ(!$9 || lowerp, $9, "Child of GENFOR should have been begin");
                          AstNode* const itemsp = lowerp && lowerp->itemsp() ? lowerp->itemsp()->unlinkFrBackWithNext() : nullptr;
                          AstGenBlock* const blkp = new AstGenBlock{$1, lowerp ? lowerp->name() : "", nullptr, true};
                          // V3LinkDot detects BEGIN(GENFOR(...)) as a special case
                          AstNode* initp = $3;
                          AstNode* const varp = $3;
                          if (VN_IS(varp, Var)) {  // Genvar
                                initp = varp->nextp();
                                initp->unlinkFrBackWithNext();  // Detach 2nd from varp, make 1st init
                                blkp->addItemsp(varp);
                          }
                          // Statements are under 'genforp' as instances under this
                          // for loop won't get an extra layer of hierarchy tacked on
                          blkp->genforp(new AstGenFor{$1, initp, $5, $7, itemsp});
                          $$ = blkp;
                          DEL(lowerp);
                        }
        ;

c_loop_generate_construct:  // IEEE: loop_generate_construct (for checkers)
                                 yFOR '(' genvar_initialization ';' expr ';' genvar_iteration ')' c_generate_block_or_null                         {                           AstGenBlock* lowerp = VN_CAST($9, GenBlock);                           UASSERT_OBJ(!$9 || lowerp, $9, "Child of GENFOR should have been begin");                           AstNode* const itemsp = lowerp && lowerp->itemsp() ? lowerp->itemsp()->unlinkFrBackWithNext() : nullptr;                           AstGenBlock* const blkp = new AstGenBlock{$1, lowerp ? lowerp->name() : "", nullptr, true};                           AstNode* initp = $3;                           AstNode* const varp = $3;                           if (VN_IS(varp, Var)) {                                 initp = varp->nextp();                                 initp->unlinkFrBackWithNext();                                 blkp->addItemsp(varp);                           }                           blkp->genforp(new AstGenFor{$1, initp, $5, $7, itemsp});                           $$ = blkp;                           DEL(lowerp);                         }      // {copied}
        ;

genvar_initialization:   // ==IEEE: genvar_initialization
                varRefBase '=' expr                     { $$ = new AstAssign{$2, $1, $3}; }
        |       yGENVAR genvar_identifierDecl '=' constExpr
                        { $$ = $2; AstNode::addNext<AstNode, AstNode>($$,
                                       new AstAssign{$3, new AstVarRef{$2->fileline(), $2, VAccess::WRITE}, $4}); }
        ;

genvar_iteration:        // ==IEEE: genvar_iteration
                varRefBase '='          expr
                        { $$ = new AstAssign{$2, $1, $3}; }
        |       varRefBase yP_PLUSEQ    expr
                        { $$ = new AstAssign{$2, $1, new AstAdd{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_MINUSEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstSub{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_TIMESEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstMul{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_DIVEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstDiv{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_MODEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstModDiv{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_ANDEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstAnd{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_OREQ      expr
                        { $$ = new AstAssign{$2, $1, new AstOr{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_XOREQ     expr
                        { $$ = new AstAssign{$2, $1, new AstXor{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_SLEFTEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstShiftL{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_SRIGHTEQ  expr
                        { $$ = new AstAssign{$2, $1, new AstShiftR{$2, $1->cloneTreePure(true), $3}}; }
        |       varRefBase yP_SSRIGHTEQ expr
                        { $$ = new AstAssign{$2, $1, new AstShiftRS{$2, $1->cloneTreePure(true), $3}}; }
        //                      // inc_or_dec_operator
        |       yP_PLUSPLUS   varRefBase
                        { $$ = new AstAssign{$1, $2, new AstAdd{$1, $2->cloneTreePure(true),
                                                                new AstConst{$1, AstConst::StringToParse{}, "'b1"}}}; }
        |       yP_MINUSMINUS varRefBase
                        { $$ = new AstAssign{$1, $2, new AstSub{$1, $2->cloneTreePure(true),
                                                                new AstConst{$1, AstConst::StringToParse{}, "'b1"}}}; }
        |       varRefBase yP_PLUSPLUS
                        { $$ = new AstAssign{$2, $1, new AstAdd{$2, $1->cloneTreePure(true),
                                                                new AstConst{$2, AstConst::StringToParse{}, "'b1"}}}; }
        |       varRefBase yP_MINUSMINUS
                        { $$ = new AstAssign{$2, $1, new AstSub{$2, $1->cloneTreePure(true),
                                                                new AstConst{$2, AstConst::StringToParse{}, "'b1"}}}; }
        ;

case_generate_itemList:  // IEEE: { case_generate_itemList }
                case_generate_item                   { $$ = $1; }
        |       case_generate_itemList case_generate_item         { $$ = $1; $1->addNext($2); }
        ;

c_case_generate_itemList:  // IEEE: { case_generate_item } (for checkers)
                                 c_case_generate_item                   { $$ = $1; }         |       c_case_generate_itemList c_case_generate_item         { $$ = $1; $1->addNext($2); }       // {copied}
        ;

case_generate_item:      // ==IEEE: case_generate_item
                caseCondList colon generate_block_or_null    { $$ = new AstGenCaseItem{$2, $1, $3}; }
        |       yDEFAULT colon generate_block_or_null        { $$ = new AstGenCaseItem{$1, nullptr, $3}; }
        |       yDEFAULT generate_block_or_null              { $$ = new AstGenCaseItem{$1, nullptr, $2}; }
        ;

c_case_generate_item:  // IEEE: case_generate_item (for checkers)
                                 caseCondList colon c_generate_block_or_null    { $$ = new AstGenCaseItem{$2, $1, $3}; }         |       yDEFAULT colon c_generate_block_or_null        { $$ = new AstGenCaseItem{$1, nullptr, $3}; }         |       yDEFAULT c_generate_block_or_null              { $$ = new AstGenCaseItem{$1, nullptr, $2}; }   // {copied}
        ;

//************************************************
// Assignments and register declarations

assignList:
                assignOne                               { $$ = $1; }
        |       assignList ',' assignOne                { $$ = $1->addNext($3); }
        ;

assignOne:
                variable_lvalue '=' expr                { AstAssignW* const ap = new AstAssignW{$2, $1, $3};
                                                          $$ = new AstAlways{ap}; }
        ;

delay_or_event_controlE:  // IEEE: delay_or_event_control plus empty
                /* empty */                             { $$ = nullptr; }
        |       delay_control                           { $$ = $1; }
        |       event_control                           { $$ = $1; }
        |       yREPEAT '(' expr ')' event_control
                        { $$ = $5; BBUNSUP($1, "Unsupported: repeat event control"); }
        ;

delay_controlE:
                /* empty */                             { $$ = nullptr; }
        |       delay_control                           { $$ = $1; }
        ;

delay_control:   //== IEEE: delay_control
                '#' delay_value
                        { $$ = new AstDelay{$<fl>1, $2, false}; }
        |       '#' '(' minTypMax ')'
                        { $$ = new AstDelay{$<fl>1, $3, false}; }
        |       '#' '(' minTypMax ',' minTypMax ')'
                        { $$ = new AstDelay{$<fl>1, $3, false}; RISEFALLDLYUNSUP($3); DEL($5); }
        |       '#' '(' minTypMax ',' minTypMax ',' minTypMax ')'
                        { $$ = new AstDelay{$<fl>1, $5, false}; RISEFALLDLYUNSUP($5); DEL($3); DEL($7); }
        ;

delay_value:         // ==IEEE:delay_value
        //                      // IEEE: ps_identifier
                idClass                                 { $$ = $1; }
        |       yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }
        |       yaFLOATNUM                              { $$ = new AstConst{$<fl>1, AstConst::RealDouble{}, $1}; }
        |       timeNumAdjusted                         { $$ = $1; }
        |       y1STEP                                  { $$ = new AstConst{$<fl>1, AstConst::OneStep{}}; }
        ;

delayExpr:
                expr                                    { $$ = $1; }
        ;

minTypMax:           // IEEE: mintypmax_expression and constant_mintypmax_expression
                delayExpr                               { $$ = $1; }
        |       delayExpr ':' delayExpr ':' delayExpr   { $$ = $3; MINTYPMAXDLYUNSUP($3); DEL($1); DEL($5); }
        ;

minTypMaxE:
                /*empty*/                               { $$ = nullptr; }
        |       minTypMax                               { $$ = $1; }
        ;

netSigList:               // IEEE: list_of_port_identifiers
                netSig                                  { $$ = $1; }
        |       netSigList ',' netSig                   { $$ = $1; $1->addNext($3); }
        ;

netSig:                   // IEEE: net_decl_assignment -  one element from list_of_port_identifiers
                netId variable_dimensionListE sigAttrListE
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3); }
        |       netId variable_dimensionListE sigAttrListE '=' expr
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3);
                          AstDelay* const delayp = $$->delayp() ? $$->delayp()->unlinkFrBack() : nullptr;
                          AstAssignW* const assignp = new AstAssignW{$4, new AstParseRef{$<fl>1, *$1}, $5, delayp};
                          if (GRAMMARP->m_netStrengthp) assignp->strengthSpecp(GRAMMARP->m_netStrengthp->cloneTree(false));
                          AstNode::addNext<AstNode, AstNode>($$, new AstAlways{assignp}); }
        ;

netId:
                id/*new-net*/                           { $$ = $1; $<fl>$ = $<fl>1; }
        |       idSVKwd                                 { $$ = $1; $<fl>$ = $<fl>1; }
        ;

sigAttrScope:
                yVL_PUBLIC_FLAT_RW_ON_SNS attr_event_control
                                                        { GRAMMARP->createScopedSigAttr(VAttrType::VAR_PUBLIC_FLAT_RW);
                                                          v3Global.dpi(true); DEL($2); }
        |       yVL_PUBLIC_ON                           { GRAMMARP->createScopedSigAttr(VAttrType::VAR_PUBLIC); }
        |       yVL_PUBLIC_FLAT_ON                      { GRAMMARP->createScopedSigAttr(VAttrType::VAR_PUBLIC_FLAT); }
        |       yVL_PUBLIC_FLAT_RD_ON                   { GRAMMARP->createScopedSigAttr(VAttrType::VAR_PUBLIC_FLAT_RD); }
        |       yVL_PUBLIC_FLAT_RW_ON                   { GRAMMARP->createScopedSigAttr(VAttrType::VAR_PUBLIC_FLAT_RW); }
        |       yVL_PUBLIC_OFF                          { GRAMMARP->setScopedSigAttr(nullptr); }
        ;

sigAttrListE: // Scoped Attributes are added to explicit attributes
                /* empty */                             { $$ = nullptr; }
        |       sigAttrList                             { $$ = $1; }
        ;

sigAttrList:
                sigAttr                                 { $$ = $1; }
        |       sigAttrList sigAttr                     { $$ = addNextNull($1, $2); }
        ;

sigAttr:
                yVL_CLOCKER                             { $$ = nullptr; /* Historical, now has no effect */ }
        |       yVL_NO_CLOCKER                          { $$ = nullptr; /* Historical, now has no effect */ }
        |       yVL_CLOCK_ENABLE                        { $$ = nullptr; /* Historical, now has no effect */ }
        |       yVL_FORCEABLE                           { $$ = new AstAttrOf{$1, VAttrType::VAR_FORCEABLE}; }
        |       yVL_PUBLIC                              { $$ = new AstAttrOf{$1, VAttrType::VAR_PUBLIC}; v3Global.dpi(true); }
        |       yVL_PUBLIC_FLAT                         { $$ = new AstAttrOf{$1, VAttrType::VAR_PUBLIC_FLAT}; v3Global.dpi(true); }
        |       yVL_PUBLIC_FLAT_RD                      { $$ = new AstAttrOf{$1, VAttrType::VAR_PUBLIC_FLAT_RD}; v3Global.dpi(true); }
        |       yVL_PUBLIC_FLAT_RW attr_event_controlE  { $$ = new AstAttrOf{$1, VAttrType::VAR_PUBLIC_FLAT_RW}; v3Global.dpi(true); DEL($2); }
        |       yVL_ISOLATE_ASSIGNMENTS                 { $$ = new AstAttrOf{$1, VAttrType::VAR_ISOLATE_ASSIGNMENTS}; }
        |       yVL_SC_BIGUINT                          { $$ = new AstAttrOf{$1, VAttrType::VAR_SC_BIGUINT}; }
        |       yVL_SC_BV                               { $$ = new AstAttrOf{$1, VAttrType::VAR_SC_BV}; }
        |       yVL_SFORMAT                             { $$ = new AstAttrOf{$1, VAttrType::VAR_SFORMAT}; }
        |       yVL_SPLIT_VAR                           { $$ = new AstAttrOf{$1, VAttrType::VAR_SPLIT_VAR}; }
        ;

rangeListE:         // IEEE: [{packed_dimension}]
                /* empty */                             { $$ = nullptr; }
        |       rangeList                               { $$ = $1; }
        ;

rangeList:          // IEEE: {packed_dimension}
                anyrange                                { $$ = $1; }
        |       rangeList anyrange                      { $$ = $1->addNext($2); }
        ;

anyrange:
                '[' constExpr ':' constExpr ']'         { $$ = new AstRange{$1, $2, $4}; }
        ;

part_select_rangeList:  // IEEE: part_select_range (as used after function calls)
                part_select_range                        { $$ = $1; }
        |       part_select_rangeList part_select_range  { $$ = GRAMMARP->scrubSel($1, $2); }
        ;

part_select_range:
                '[' expr ']'
                        { $$ = new AstSelBit{$1, new AstParseHolder{$1}, $2}; }
        |       '[' constExpr ':' constExpr ']'
                        { $$ = new AstSelExtract{$1, new AstParseHolder{$1}, $2, $4}; }
        |       '[' expr yP_PLUSCOLON constExpr ']'
                        { $$ = new AstSelPlus{$1, new AstParseHolder{$1}, $2, $4}; }
        |       '[' expr yP_MINUSCOLON constExpr ']'
                        { $$ = new AstSelMinus{$1, new AstParseHolder{$1}, $2, $4}; }
        ;

packed_dimensionListE:      // IEEE: [{ packed_dimension }]
                /* empty */                             { $$ = nullptr; }
        |       packed_dimensionList                    { $$ = $1; }
        ;

packed_dimensionList:       // IEEE: { packed_dimension }
                packed_dimension                        { $$ = $1; }
        |       packed_dimensionList packed_dimension   { $$ = $1->addNext($2); }
        ;

packed_dimension:   // ==IEEE: packed_dimension
                anyrange                                { $$ = $1; }
        |       '[' ']'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: [] dimensions"); }
        ;

//************************************************
// Parameters

param_assignment:         // ==IEEE: param_assignment
        //                      // IEEE: constant_param_expression
        //                      // constant_param_expression: '$' is in expr
                id/*new-parameter*/ variable_dimensionListE sigAttrListE exprOrDataTypeEqE
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3);
                          if ($4) $$->valuep($4);
                          else if (!GRAMMARP->m_pinAnsi)
                              $$->v3warn(PARAMNODEFAULT, "Parameter without default requires"
                                         " ANSI-style parameter list (IEEE 1800-2023 6.20.1): "
                                         << $$->prettyNameQ()); }
        ;

list_of_param_assignments:        // ==IEEE: list_of_param_assignments
                param_assignment                        { $$ = $1; }
        |       list_of_param_assignments ',' param_assignment  { $$ = $1->addNext($3); }
        ;

type_assignment:          // ==IEEE: type_assignment
        //                      // note exprOrDataType being a data_type is only for yPARAMETER yTYPE
        //                      // Using exprOrDataType allows hierarchical refs like if0.rq_t
        //                      // which get resolved to types during linking
                idAny/*new-parameter*/ sigAttrListE
                        { $$ = VARDONEA($<fl>1, *$1, nullptr, $2); }
        |       idAny/*new-parameter*/ sigAttrListE '=' exprOrDataType
                        { $$ = VARDONEA($<fl>1, *$1, nullptr, $2);
                          // V3LinkParse will wrap this in RequireDType when creating ParamTypeDType
                          $$->valuep($4); }
        ;

list_of_type_assignments:         // ==IEEE: list_of_type_assignments
                type_assignment                         { $$ = $1; }
        |       list_of_type_assignments ',' type_assignment
                        { $$ = addNextNull($1, $3); }
        ;

list_of_defparam_assignments:    //== IEEE: list_of_defparam_assignments
                defparam_assignment                     { $$ = $1; }
        |       list_of_defparam_assignments ',' defparam_assignment
                        { $$ = addNextNull($1, $3); }
        ;

defparam_assignment:     // ==IEEE: defparam_assignment
                defparamIdRange '.' defparamIdRange '=' expr
                        { $$ = new AstDefParam{$4, *$1, *$3, $5}; }
        |       defparamIdRange '=' expr
                        { $$ = nullptr; BBUNSUP($2, "Unsupported: defparam with no dot");
                          DEL($3); }
        |       defparamIdRange '.' defparamIdRange '.' defparamIdRangeList '=' expr
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: defparam with more than one dot");
                          DEL($7); }
        ;

defparamIdRangeList:  // IEEE: part of defparam_assignment
                defparamIdRange                         { $$ = $1; }
        |       defparamIdRangeList '.' defparamIdRange  { $$ = $3; }
        ;

defparamIdRange:  // IEEE: part of defparam_assignment
                idAny
                        { $$ = $1; }
        |       idAny part_select_rangeList
                        { $$ = $1; BBUNSUP($2, "Unsupported: defparam with arrayed instance");
                          DEL($2); }
        ;

//************************************************
// Instances
// We don't know identifier types, so this matches all module,udp,etc instantiation
//   module_id      [#(params)]   name  (pins) [, name ...] ;   // module_instantiation
//   gate (strong0) [#(delay)]   [name] (pins) [, (pins)...] ;  // gate_instantiation
//   program_id     [#(params}]   name ;                        // program_instantiation
//   interface_id   [#(params}]   name ;                        // interface_instantiation
//   checker_id                   name  (pins) ;                // checker_instantiation

etcInst:                 // IEEE: module_instantiation + gate_instantiation + udp_instantiation
                instDecl                                { $$ = $1; }
        |       gateDecl                                { $$ = $1; }
        ;

instDecl:
        //                      // Disambigurated from data_declaration based on
        //                      // idInst which is found as IEEE requires a later '('
                idInst parameter_value_assignmentInstE
        /*mid*/         { INSTPREP($<fl>1, *$1, $2); }
        /*cont*/    instnameList ';'
                        { $$ = $4;
                          GRAMMARP->m_impliedDecl = false;
                          if (GRAMMARP->m_instParamp) {
                              VL_DO_CLEAR(GRAMMARP->m_instParamp->deleteTree(),
                                          GRAMMARP->m_instParamp = nullptr);
                          } }
        //
        //                      // IEEE: part of udp_instance when no name_of_instance
        //                      // Note no unpacked dimension nor list of instances
        |       id
        /*mid*/         { INSTPREP($<fl>1, *$1, nullptr); }
        /*cont*/    instnameParenUdpn ';'
                        { $$ = $3; GRAMMARP->m_impliedDecl = false; }
        ;

mpInstnameList:          // Similar to instnameList, but for modport instantiations which have no parenthesis
                mpInstnameParen                         { $$ = $1; }
        |       mpInstnameList ',' mpInstnameParen      { $$ = $1->addNext($3); }
        ;

mpInstnameParen:         // Similar to instnameParen, but for modport instantiations which have no parenthesis
                id instRangeListE sigAttrListE          { $$ = VARDONEA($<fl>1, *$1, $2, $3); }
        ;

instnameList:
                instnameParen                           { $$ = $1; }
        |       instnameList ',' instnameParen          { $$ = $1->addNext($3); }
        ;

instnameParen:
                id instRangeListE '(' instPinListE ')'
                        { $$ = GRAMMARP->createCell($<fl>1, *$1, $4, $2); }
        ;

instnameParenUdpn:  // IEEE: part of udp_instance when no name_of_instance
                '(' instPinListE ')'  // When UDP has empty name, unpacked dimensions must not be used
                        { $$ = GRAMMARP->createCell($<fl>1, "", $2, nullptr); }
        ;

instRangeListE:
                /* empty */                             { $$ = nullptr; }
        |       instRangeList                           { $$ = $1; }
        ;

instRangeList:
                instRange                               { $$ = $1; }
        |       instRangeList instRange                 { $$ = addNextNull($1, $2); }
        ;

instRange:
                '[' constExpr ']'
                        { $$ = new AstRange{$1, new AstConst{$1, 0}, new AstSub{$1, $2, new AstConst{$1, 1}}, true}; }
        |       '[' constExpr ':' constExpr ']'
                        { $$ = new AstRange{$1, $2, $4}; }
        ;

instParamListE:
                { GRAMMARP->pinPush(); } instParamItListE   { $$ = $2; GRAMMARP->pinPop(CRELINE()); }
        ;

instPinListE:
                { VARRESET_LIST(UNKNOWN); } instPinItListE   { $$ = $2; VARRESET_NONLIST(UNKNOWN); }
        ;

instParamItListE:         // IEEE: list_of_parameter_value_assignments/list_of_parameter_assignments
        //                      // Empty gets a node, to track class reference of #()
                /*empty*/                               { $$ = new AstPin{CRELINE(), PINNUMINC(), "", nullptr}; }
        |       instParamItList                         { $$ = $1; }
        ;

instParamItList:          // IEEE: list_of_parameter_value_assignments/list_of_parameter_assignments
                instParamItem                           { $$ = $1; }
        |       instParamItList ',' instParamItem       { $$ = addNextNull($1, $3); }
        ;

instPinItListE:           // IEEE: list_of_port_connections
                instPinItemE                            { $$ = $1; }
        |       instPinItListE ',' instPinItemE         { $$ = addNextNull($1, $3); }
        ;

instParamItem:            // IEEE: named_parameter_assignment + empty
        //                      // Note empty is not allowed in parameter lists
                yP_DOTSTAR                              { $$ = new AstPin{$1, PINNUMINC(), ".*", nullptr}; }
        |       '.' idAny '(' ')'
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, nullptr};
                          $$->svDotName(true); }
        |       '.' idSVKwd
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2,
                                          new AstParseRef{$<fl>2, *$2, nullptr, nullptr}};
                          $$->svDotName(true); $$->svImplicit(true); }
        |       '.' idAny
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2,
                                          new AstParseRef{$<fl>2, *$2, nullptr, nullptr}};
                          $$->svDotName(true); $$->svImplicit(true); }
        //                      // mintypmax is expanded here, as it might be a UDP or gate primitive
        //                      // data_type for 'parameter type' hookups
        |       '.' idAny '(' exprOrDataType ')'
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, $4};
                          $$->svDotName(true); }
        //UNSUP | '.' idAny '(' exprOrDataType/*expr*/ ':' expr ')'
        //UNSUP          { MINTYPMAXDLYUNSUP($4); DEL($4);
        //UNSUP            $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, $6};
        //UNSUP            $$->svDotName(true); }
        //UNSUP | '.' idAny '(' exprOrDataType/*expr*/ ':' expr ':' expr ')'
        //UNSUP          { MINTYPMAXDLYUNSUP($4); DEL($4); DEL($8);
        //UNSUP            $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, $6};
        //UNSUP            $$->svDotName(true); }
        //                      // data_type for 'parameter type' hookups
        |       exprOrDataType
                        { $$ = new AstPin{FILELINE_OR_CRE($1), PINNUMINC(), "", $1}; }
        //UNSUP | exprOrDataType/*expr*/ ':' expr
        //UNSUP          { MINTYPMAXDLYUNSUP($1); DEL($1);
        //UNSUP            $$ = new AstPin{FILELINE_OR_CRE($3), PINNUMINC(), "", $3}; }
        //UNSUP | exprOrDataType/*expr*/ ':' expr ':' expr
        //UNSUP          { MINTYPMAXDLYUNSUP($1); DEL($1); DEL($5);
        //UNSUP            $$ = new AstPin{FILELINE_OR_CRE($3), PINNUMINC(), "", $3}; }
        ;

instPinItemE:             // IEEE: named_port_connection + empty
        //                      // Note empty can match either () or (,); V3LinkCells cleans up ()
                /* empty: ',,' is legal */              { $$ = new AstPin{CRELINE(), PINNUMINC(), "", nullptr}; }
        |       yP_DOTSTAR                              { $$ = new AstPin{$1, PINNUMINC(), ".*", nullptr}; }
        |       '.' idAny '(' ')'
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, nullptr};
                          $$->svDotName(true); }
        |       '.' idSVKwd
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2,
                                          new AstParseRef{$<fl>2, *$2, nullptr, nullptr}};
                          $$->svDotName(true); $$->svImplicit(true); }
        |       '.' idAny
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2,
                                          new AstParseRef{$<fl>2, *$2, nullptr, nullptr}};
                          $$->svDotName(true); $$->svImplicit(true); }
        //                      // mintypmax is expanded here, as it might be a UDP or gate primitive
        //UNSUP               pev_expr below
        |       '.' idAny '(' expr ')'
                        { $$ = new AstPin{$<fl>2, PINNUMINC(), *$2, $4};
                          $$->svDotName(true); }
        //UNSUP '.' idAny '(' pev_expr ':' expr ')'     { }
        //UNSUP '.' idAny '(' pev_expr ':' expr ':' expr ')' { }
        //
        |       expr                                    { $$ = new AstPin{FILELINE_OR_CRE($1), PINNUMINC(), "", $1}; }
        //UNSUP expr ':' expr                           { }
        //UNSUP expr ':' expr ':' expr                  { }
        ;

//************************************************
// EventControl lists

attr_event_controlE:
                /* empty */                             { $$ = nullptr; }
        |       attr_event_control                      { $$ = $1; }
        ;

attr_event_control:   // ==IEEE: event_control
                '@' '(' event_expression ')'            { $$ = new AstSenTree{$1, $3}; }
        |       '@' '(' '*' ')'                         { $$ = GRAMMARP->createSenTreeDotStar($1); }
        |       '@' '*'                                 { $$ = GRAMMARP->createSenTreeDotStar($1); }
        ;

event_control:        // ==IEEE: event_control
        // UNSUP: Needs alignment with IEEE event_control and clocking_event
                '@' '(' '*' ')'                         { $$ = GRAMMARP->createSenTreeDotStar($1); }
        |       '@' '*'                                 { $$ = GRAMMARP->createSenTreeDotStar($1); }
        //                      // IEEE: clocking_event
        |       '@' '(' event_expression ')'            { $$ = new AstSenTree{$1, $3}; }
        //                      // IEEE: hierarchical_event_identifier
        //                      // UNSUP below should be idClassSel
        |       '@' senitemVar                          { $$ = new AstSenTree{$1, $2}; } /* For events only */
        //                      // IEEE: sequence_instance
        //                      // sequence_instance without parens matches idClassSel above.
        //                      // Ambiguity: "'@' sequence (-for-sequence" versus
        //                      // expr:delay_or_event_controlE "'@' id (-for-expr
        //                      // For now we avoid this, as it's very unlikely someone would mix
        //                      // 1995 delay with a sequence with parameters.
        //                      // Alternatively split this out of event_control, and delay_or_event_controlE
        //                      // and anywhere delay_or_event_controlE is called allow two expressions
        //UNSUP '@' idClassSel '(' list_of_argumentsE ')'       { }
        ;

event_expression:     // IEEE: event_expression - split over several
        //UNSUP                 // Below are all removed
                senitem                                 { $$ = $1; }
        |       event_expression yOR senitem            { $$ = addNextNull($1, $3); }
        |       event_expression ',' senitem            { $$ = addNextNull($1, $3); } /* Verilog 2001 */
        //UNSUP                 // Above are all removed, replace with:
        //UNSUP ev_expr                                 { $$ = $1; }
        //UNSUP event_expression ',' ev_expr %prec yOR  { $$ = addNextNull($1, $3); }
        ;

senitem:              // IEEE: part of event_expression, non-'OR' ',' terms
                senitemEdge                             { $$ = $1; }
        |       expr
                        { $$ = new AstSenItem{$<fl>1, VEdgeType::ET_CHANGED, $1}; }
        |       expr yIFF expr
                        { $$ = new AstSenItem{$<fl>1, VEdgeType::ET_CHANGED, $1, $3}; }
        ;

senitemVar:
                idClassSel
                        { $$ = new AstSenItem{$1->fileline(), VEdgeType::ET_CHANGED, $1}; }
        ;

senitemEdge:          // IEEE: part of event_expression
                yPOSEDGE expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_POSEDGE, $2}; }
        |       yNEGEDGE expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_NEGEDGE, $2}; }
        |       yEDGE expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_BOTHEDGE, $2}; }
        |       yPOSEDGE expr yIFF expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_POSEDGE, $2, $4}; }
        |       yNEGEDGE expr yIFF expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_NEGEDGE, $2, $4}; }
        |       yEDGE expr yIFF expr
                        { $$ = new AstSenItem{$1, VEdgeType::ET_BOTHEDGE, $2, $4}; }
        ;

//************************************************
// Statements

seq_block:               // ==IEEE: seq_block
        //                      // IEEE doesn't allow declarations in unnamed blocks, but several simulators do.
        //                      // So need AstBegin's even if unnamed to scope variables down
                yBEGIN startLabelE blockDeclListE stmtListE yEND endLabelE
                        {
                            $$ = new AstBegin{$1, $2 ? *$2 : "", nullptr, false};
                            GRAMMARP->endLabel($<fl>6, $$, $6);
                            $$->addDeclsp($3);
                            $$->addStmtsp($4);
                        }
        ;

seq_blockPreId:          // IEEE: seq_block, but called with leading ID
                id yP_COLON__BEGIN yBEGIN blockDeclListE stmtListE yEND endLabelE
                        {
                            $$ = new AstBegin{$3, *$1, nullptr, false};
                            GRAMMARP->endLabel($<fl>7, $$, $7);
                            $$->addDeclsp($4);
                            $$->addStmtsp($5);
                        }
        ;

par_blockJoin:
                yJOIN       { $$ = VJoinType::JOIN; }
        |       yJOIN_ANY   { $$ = VJoinType::JOIN_ANY; }
        |       yJOIN_NONE  { $$ = VJoinType::JOIN_NONE; }
        ;

par_block:               // ==IEEE: par_block
                yFORK startLabelE blockDeclListE stmtListE par_blockJoin endLabelE
                        {
                            AstFork* const forkp = new AstFork{$1, $5, $2 ? *$2 : ""};
                            GRAMMARP->endLabel($<fl>6, forkp, $6);
                            forkp->addDeclsp($3);
                            $$ = V3ParseGrammar::wrapFork(PARSEP, forkp, $4);
                        }
        ;

par_blockPreId:          // ==IEEE: par_block but called with leading ID
                id yP_COLON__FORK yFORK blockDeclListE stmtListE par_blockJoin endLabelE
                        {
                            AstFork* const forkp = new AstFork{$3, $6, *$1};
                            GRAMMARP->endLabel($<fl>7, forkp, $7);
                            forkp->addDeclsp($4);
                            $$ = V3ParseGrammar::wrapFork(PARSEP, forkp, $5);
                        }
            ;

blockDeclListE:      // IEEE: [ block_item_declaration ]
                /*empty*/                               { $$ = nullptr; }
        |       blockDeclListE block_item_declaration   { $$ = addNextNull($1, $2); }
        |       error ';'                               { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

block_item_declaration:  // ==IEEE: block_item_declaration
                data_declaration                        { $$ = $1; }
        |       parameter_declaration ';'               { $$ = $1; }
        |       let_declaration                         { $$ = $1; }
        ;

stmtListE:
                /*empty*/                               { $$ = nullptr; }
        |       stmtList                                { $$ = $1; }
        ;

stmtList:
                stmt                               { $$ = $1; }
        |       stmtList stmt                      { $$ = addNextNull($1, $2); }
        //
        |       stmtList error ';'                      { $$ = $1; }  // LCOV_EXCL_LINE
        ;

stmt:                    // IEEE: statement + seq_block + par_block
                statement_item                          { $$ = $1; }
        //                      // S05 block creation rule
        |       id/*block_identifier*/ ':' statement_item       { $$ = new AstBegin{$<fl>1, *$1, $3, false}; }
        //                      // from _or_null
        |       ';'                                     { $$ = nullptr; }
        //                      // labeled par_block/seq_block with leading ':'
        |       seq_blockPreId                          { $$ = $1; }
        |       par_blockPreId                          { $$ = $1; }
        ;

statement_item:          // IEEE: statement_item
        //                      // IEEE: operator_assignment
                foperator_assignment ';'                { $$ = $1; }
        //
        //                      // IEEE: blocking_assignment
        //                      // 1800-2009 restricts LHS of assignment to new to not have a range
        //                      // This is ignored to avoid conflicts
        |       fexprLvalue yP_EQ__NEW dynamic_array_new ';'   { $$ = new AstAssign{$2, $1, $3}; }
        |       fexprLvalue yP_EQ__NEW class_new ';'    { $$ = new AstAssign{$2, $1, $3}; }
        //                      // IEEE: inc_or_dec_expression
        |       finc_or_dec_expression ';'              { $$ = new AstStmtExpr{$<fl>1, $1}; }
        //
        //                      // IEEE: nonblocking_assignment
        |       fexprLvalue yP_LTE delay_or_event_controlE expr ';'
                        { $$ = new AstAssignDly{$2, $1, $4, $3}; }
        //                      // IEEE: clocking_drive ';'
        |       fexprLvalue yP_LTE cycle_delay expr ';'
                        { $$ = new AstAssignDly{$2, $1, $4, $3}; }
        //UNSUP cycle_delay fexprLvalue yP_LTE ';'      { UNSUP }
        |       yASSIGN idClassSel '=' delay_or_event_controlE expr ';'
                        { $$ = new AstAssignCont{$1, $2, $5, $4}; }
        |       yDEASSIGN variable_lvalue ';'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: Verilog 1995 deassign"); DEL($2); }
        |       yFORCE variable_lvalue '=' expr ';'
                        { $$ = new AstAssignForce{$1, $2, $4}; v3Global.setHasForceableSignals(); }
        |       yRELEASE variable_lvalue ';'
                        { $$ = new AstRelease{$1, $2}; v3Global.setHasForceableSignals(); }
        //
        //                      // IEEE: case_statement
        |       unique_priorityE caseStart caseAttrE case_itemList yENDCASE
                        { $$ = $2; if ($4) $2->addItemsp($4);
                          if ($1 == uniq_UNIQUE) $2->uniquePragma(true);
                          if ($1 == uniq_UNIQUE0) $2->unique0Pragma(true);
                          if ($1 == uniq_PRIORITY) $2->priorityPragma(true); }
        // &&& is part of expr so case_patternList aliases to case_itemList
        |       unique_priorityE caseStart caseAttrE yMATCHES case_itemList yENDCASE
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: matches (for tagged union)"); DEL($2, $5); }
        |       unique_priorityE caseStart caseAttrE yINSIDE case_inside_itemList yENDCASE
                        { $$ = $2; if ($5) $2->addItemsp($5);
                          if (!$2->caseSimple()) $4->v3error("Illegal to have inside on a casex/casez");
                          $2->caseInsideSet();
                          if ($1 == uniq_UNIQUE) $2->uniquePragma(true);
                          if ($1 == uniq_UNIQUE0) $2->unique0Pragma(true);
                          if ($1 == uniq_PRIORITY) $2->priorityPragma(true); }
        //
        //                      // IEEE: conditional_statement
        |       unique_priorityE yIF '(' expr ')' stmt     %prec prLOWER_THAN_ELSE
                        { AstIf* const newp = new AstIf{$2, $4,
                              PARSEP->newBlock($2, $6)};
                          $$ = newp;
                          if ($1 == uniq_UNIQUE) newp->uniquePragma(true);
                          if ($1 == uniq_UNIQUE0) newp->unique0Pragma(true);
                          if ($1 == uniq_PRIORITY) newp->priorityPragma(true); }
        |       unique_priorityE yIF '(' expr ')' stmt yELSE stmt
                        { AstIf* const newp = new AstIf{$2, $4,
                              PARSEP->newBlock($2, $6),
                              PARSEP->newBlock($2, $8)};
                          $$ = newp;
                          if ($1 == uniq_UNIQUE) newp->uniquePragma(true);
                          if ($1 == uniq_UNIQUE0) newp->unique0Pragma(true);
                          if ($1 == uniq_PRIORITY) newp->priorityPragma(true); }
        //
        //                      // IEEE: subroutine_call_statement
        //                      // IEEE says we then expect a function call
        //                      // (function_subroutine_callNoMethod), but rest of
        //                      // the code expects an AstTask when used as a statement,
        //                      // so parse as if task
        //                      // Alternative would be shim with new AstVoidStmt.
        |       yVOID yP_TICK '(' task_subroutine_callNoMethod ')' ';'
                        { AstNodeExpr* const exprp = $4;
                          AstNode* callp = exprp;
                          while (AstDot* const dotp = VN_CAST(callp, Dot)) callp = dotp->rhsp();
                          FileLine* const newfl = new FileLine{callp->fileline()};
                          newfl->warnOff(V3ErrorCode::IGNOREDRETURN, true);
                          callp->fileline(newfl);
                          $$ = exprp->makeStmt(); }
        |       yVOID yP_TICK '(' expr '.' task_subroutine_callNoMethod ')' ';'
                        { AstNodeExpr* const exprp = new AstDot{$5, false, $4, $6};
                          FileLine* const newfl = new FileLine{$6->fileline()};
                          newfl->warnOff(V3ErrorCode::IGNOREDRETURN, true);
                          $6->fileline(newfl);
                          $$ = exprp->makeStmt(); }
        |       yVOID yP_TICK '(' system_f_only_expr_call ')' ';'
                        { $$ = new AstStmtExpr{$<fl>4, $4};
                          FileLine* const newfl = new FileLine{$$->fileline()};
                          newfl->warnOff(V3ErrorCode::IGNOREDRETURN, true);
                          $$->fileline(newfl); }
        //                      // Any system function as a task
        |       yVOID yP_TICK '(' system_f_or_t_expr_call ')' ';'
                        { $$ = new AstStmtExpr{$<fl>4, $4};
                          FileLine* const newfl = new FileLine{$$->fileline()};
                          newfl->warnOff(V3ErrorCode::IGNOREDRETURN, true);
                          $$->fileline(newfl); }
        //
        |       task_subroutine_callNoSemi ';'          { $$ = $1; }
        //
        |       statementVerilatorPragmas               { $$ = new AstStmtPragma{$<fl>1, $1}; }
        //
        //                      // IEEE: disable_statement
        |       yDISABLE yFORK ';'                      { $$ = new AstDisableFork{$1}; }
        |       yDISABLE idDottedSel ';'
                        { $$ = new AstDisable{$1, $2};
                          PARSEP->importIfInStd($1, "process", true);
                        }
        //                      // IEEE: event_trigger
        |       yP_MINUSGT expr ';'
                        { $$ = new AstFireEvent{$1, $2, false}; }
        |       yP_MINUSGTGT delay_or_event_controlE expr ';'
                        { $$ = new AstFireEvent{$1, $3, true}; }
        //
        // do/for/forever/while loops all modelled as AstLoop
        |       yDO stmt yWHILE '(' expr ')' ';'
                        { AstLoop* const loopp = new AstLoop{$1, $2};
                          loopp->addContsp(new AstLoopTest{$<fl>5, loopp, $5});
                          $$ = loopp; }
        |       yFOR  '(' { VARRESET_NONLIST(UNKNOWN); } for_initializationE ';' exprE ';' for_stepE ')' stmt
                        { AstBegin* const blockp = new AstBegin{$1, "", $4, true};
                          AstLoop* const loopp = new AstLoop{$1};
                          if ($6) loopp->addStmtsp(new AstLoopTest{$<fl>6, loopp, $6});
                          loopp->addStmtsp($10);
                          loopp->addContsp($8);
                          blockp->addStmtsp(loopp);
                          $$ = blockp; }
        |       yFOREVER stmt
                        { AstLoop* const loopp = new AstLoop{$1, $2};
                          $$ = loopp; }
        |       yWHILE '(' expr ')' stmt
                        { AstLoop* const loopp = new AstLoop{$1};
                          loopp->addStmtsp(new AstLoopTest{$<fl>3, loopp, $3});
                          loopp->addStmtsp($5);
                          $$ = loopp; }
        // Other loop statements
        |       yREPEAT '(' expr ')' stmt          { $$ = new AstRepeat{$1, $3, $5}; }
        //                      // IEEE says array_identifier here, but dotted accepted in VMM and 1800-2009
        |       yFOREACH '(' idClassSelForeach ')' stmt
                        { $$ = new AstBegin{$1, "", new AstForeach{$1, $3, $5}, true}; }
        //
        //                      // IEEE: jump_statement
        |       yRETURN ';'                             { $$ = new AstReturn{$1}; }
        |       yRETURN expr ';'                        { $$ = new AstReturn{$1, $2}; }
        |       yBREAK ';'                              { $$ = new AstBreak{$1}; }
        |       yCONTINUE ';'                           { $$ = new AstContinue{$1}; }
        //
        |       par_block                               { $$ = $1; }
        //                      // IEEE: procedural_timing_control_statement + procedural_timing_control
        |       delay_control stmt
                        { AstNodeStmt* nextp = nullptr;
                          if ($2) {
                              if ($2->nextp()) nextp = VN_AS($2->nextp()->unlinkFrBackWithNext(), NodeStmt);
                              $1->addStmtsp($2);
                          }
                          $$ = $1;
                          addNextNull($$, nextp); }
        |       event_control stmt
                        { AstNodeStmt* nextp = nullptr;
                          if ($2 && $2->nextp()) nextp = VN_AS($2->nextp()->unlinkFrBackWithNext(), NodeStmt);
                          $$ = new AstEventControl{FILELINE_OR_CRE($1), $1, $2};
                          addNextNull($$, nextp); }
        |       cycle_delay stmt
                        { AstNodeStmt* nextp = nullptr;
                          if ($2) {
                              if ($2->nextp()) nextp = VN_AS($2->nextp()->unlinkFrBackWithNext(), NodeStmt);
                              $1->addStmtsp($2);
                          }
                          $$ = $1;
                          addNextNull($$, nextp); }
        |       seq_block                               { $$ = $1; }
        //
        //                      // IEEE: wait_statement
        |       yWAIT '(' expr ')' stmt            { $$ = new AstWait{$1, $3, $5}; }
        |       yWAIT yFORK ';'                         { $$ = new AstWaitFork{$1}; }
        //                      // action_block expanded here
        |       yWAIT_ORDER '(' vrdList ')' stmt %prec prLOWER_THAN_ELSE
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: wait_order"); DEL($3, $5); }
        |       yWAIT_ORDER '(' vrdList ')' stmt yELSE stmt
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: wait_order"); DEL($3, $5, $7);}
        |       yWAIT_ORDER '(' vrdList ')' yELSE stmt
                        { $$ = nullptr; BBUNSUP($4, "Unsupported: wait_order"); DEL($3, $6); }
        //
        //                      // IEEE: procedural_assertion_statement
        |       procedural_assertion_statement          { $$ = $1; }
        //
        |       randsequence_statement                  { $$ = $1; }
        //
        //                      // IEEE: randcase_statement
        |       yRANDCASE rand_case_itemList yENDCASE   { $$ = new AstRandCase{$1, $2}; }
        //
        //                      // IEEE: expect_property_statement
        //                      // action_block expanded here
        |       yEXPECT '(' property_spec ')' stmt %prec prLOWER_THAN_ELSE
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: expect"); DEL($3, $5); }
        |       yEXPECT '(' property_spec ')' stmt yELSE stmt
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: expect"); DEL($3, $5, $7); }
        |       yEXPECT '(' property_spec ')' yELSE stmt
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: expect"); DEL($3, $6); }
        ;

statementVerilatorPragmas:
                yVL_COVERAGE_BLOCK_OFF
                        { $$ = new AstPragma{$1, VPragmaType::COVERAGE_BLOCK_OFF}; }
        |       yVL_UNROLL_DISABLE
                        { $$ = new AstPragma{$1, VPragmaType::UNROLL_DISABLE}; }
        |       yVL_UNROLL_FULL
                        { $$ = new AstPragma{$1, VPragmaType::UNROLL_FULL}; }
        ;

foperator_assignment:    // IEEE: operator_assignment (for first part of expression)
                fexprLvalue '=' delay_or_event_controlE expr    { $$ = new AstAssign{$2, $1, $4, $3}; }
        //
        |       fexprLvalue yP_PLUSEQ    expr
                        { $$ = new AstAssign{$2, $1, new AstAdd{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_MINUSEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstSub{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_TIMESEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstMul{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_DIVEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstDiv{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_MODEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstModDiv{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_ANDEQ     expr
                        { $$ = new AstAssign{$2, $1, new AstAnd{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_OREQ      expr
                        { $$ = new AstAssign{$2, $1, new AstOr{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_XOREQ     expr
                        { $$ = new AstAssign{$2, $1, new AstXor{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_SLEFTEQ   expr
                        { $$ = new AstAssign{$2, $1, new AstShiftL{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_SRIGHTEQ  expr
                        { $$ = new AstAssign{$2, $1, new AstShiftR{$2, $1->cloneTreePure(true), $3}}; }
        |       fexprLvalue yP_SSRIGHTEQ expr
                        { $$ = new AstAssign{$2, $1, new AstShiftRS{$2, $1->cloneTreePure(true), $3}}; }
        ;

inc_or_dec_expression:   // ==IEEE: inc_or_dec_expression
        //                      // Need fexprScope instead of variable_lvalue to prevent conflict
                exprScope yP_PLUSPLUS
                        { $<fl>$ = $<fl>1; $$ = new AstPostAdd{$2, new AstConst{$2, AstConst::StringToParse{}, "'b1"},
                                                               // Purity checked in V3LinkInc
                                                               $1, $1->cloneTree(true)}; }
        |       exprScope yP_MINUSMINUS
                        { $<fl>$ = $<fl>1; $$ = new AstPostSub{$2, new AstConst{$2, AstConst::StringToParse{}, "'b1"},
                                                               // Purity checked in V3LinkInc
                                                               $1, $1->cloneTree(true)}; }
        //                      // Need expr instead of variable_lvalue to prevent conflict
        |       yP_PLUSPLUS     expr
                        { $<fl>$ = $<fl>1; $$ = new AstPreAdd{$1, new AstConst{$1, AstConst::StringToParse{}, "'b1"},
                                                              // Purity checked in V3LinkInc
                                                              $2, $2->cloneTree(true)}; }
        |       yP_MINUSMINUS   expr
                        { $<fl>$ = $<fl>1; $$ = new AstPreSub{$1, new AstConst{$1, AstConst::StringToParse{}, "'b1"},
                                                              // Purity checked in V3LinkInc
                                                              $2, $2->cloneTree(true)}; }
        ;

finc_or_dec_expression:  // ==IEEE: inc_or_dec_expression
                                 fexprScope yP_PLUSPLUS                         { $<fl>$ = $<fl>1; $$ = new AstPostAdd{$2, new AstConst{$2, AstConst::StringToParse{}, "'b1"},                                                                $1, $1->cloneTree(true)}; }         |       fexprScope yP_MINUSMINUS                         { $<fl>$ = $<fl>1; $$ = new AstPostSub{$2, new AstConst{$2, AstConst::StringToParse{}, "'b1"},                                                                $1, $1->cloneTree(true)}; }         |       yP_PLUSPLUS     expr                         { $<fl>$ = $<fl>1; $$ = new AstPreAdd{$1, new AstConst{$1, AstConst::StringToParse{}, "'b1"},                                                               $2, $2->cloneTree(true)}; }         |       yP_MINUSMINUS   expr                         { $<fl>$ = $<fl>1; $$ = new AstPreSub{$1, new AstConst{$1, AstConst::StringToParse{}, "'b1"},                                                               $2, $2->cloneTree(true)}; }         // {copied}
        ;

sinc_or_dec_expression:  // IEEE: inc_or_dec_expression (for sequence_expression)
                                 sexprScope yP_PLUSPLUS                         { $<fl>$ = $<fl>1; $$ = new AstPostAdd{$2, new AstConst{$2, AstConst::StringToParse{}, "'b1"},                                                                $1, $1->cloneTree(true)}; }         |       sexprScope yP_MINUSMINUS                         { $<fl>$ = $<fl>1; $$ = new AstPostSub{$2, new AstConst{$2, AstConst::StringToParse{}, "'b1"},                                                                $1, $1->cloneTree(true)}; }         |       yP_PLUSPLUS     expr                         { $<fl>$ = $<fl>1; $$ = new AstPreAdd{$1, new AstConst{$1, AstConst::StringToParse{}, "'b1"},                                                               $2, $2->cloneTree(true)}; }         |       yP_MINUSMINUS   expr                         { $<fl>$ = $<fl>1; $$ = new AstPreSub{$1, new AstConst{$1, AstConst::StringToParse{}, "'b1"},                                                               $2, $2->cloneTree(true)}; }         // {copied}
        ;

pinc_or_dec_expression:  // IEEE: inc_or_dec_expression (for property_expression)
                                 pexprScope yP_PLUSPLUS                         { $<fl>$ = $<fl>1; $$ = new AstPostAdd{$2, new AstConst{$2, AstConst::StringToParse{}, "'b1"},                                                                $1, $1->cloneTree(true)}; }         |       pexprScope yP_MINUSMINUS                         { $<fl>$ = $<fl>1; $$ = new AstPostSub{$2, new AstConst{$2, AstConst::StringToParse{}, "'b1"},                                                                $1, $1->cloneTree(true)}; }         |       yP_PLUSPLUS     expr                         { $<fl>$ = $<fl>1; $$ = new AstPreAdd{$1, new AstConst{$1, AstConst::StringToParse{}, "'b1"},                                                               $2, $2->cloneTree(true)}; }         |       yP_MINUSMINUS   expr                         { $<fl>$ = $<fl>1; $$ = new AstPreSub{$1, new AstConst{$1, AstConst::StringToParse{}, "'b1"},                                                               $2, $2->cloneTree(true)}; }         // {copied}
        ;

//UNSUPev_inc_or_dec_expression<nodeExprp>:  // IEEE: inc_or_dec_expression (for ev_expr)
//UNSUP         BISONPRE_COPY(inc_or_dec_expression,{s//ev_/g})      // {copied}
//UNSUP ;

//UNSUPpev_inc_or_dec_expression<nodeExprp>:  // IEEE: inc_or_dec_expression (for pev_expr)
//UNSUP         BISONPRE_COPY(inc_or_dec_expression,{s//pev_/g})     // {copied}
//UNSUP ;

class_new:    // IEEE: class_new
        //                      // See V3ParseImp::tokenPipeScanEqNew that searches for '=' ... yNEW__LEX
                class_newNoScope
                        { $$ = $1; }
        //                      // Special precedence so (...) doesn't match expr
        //                      // A scope is not legal in front of a AstNewCopy
        |       packageClassScopeNoId yNEW__ETC
                        { $$ = AstDot::newIfPkg($<fl>2, $1, new AstNew{$2,  nullptr, true}); }
        |       packageClassScopeNoId yNEW__PAREN '(' list_of_argumentsE ')'
                        { $$ = AstDot::newIfPkg($<fl>2, $1, new AstNew{$2, $4, true}); }
        ;

class_newNoScope:    // IEEE: class_new but no packageClassScope
        //                      // Special precedence so (...) doesn't match expr
                yNEW__ETC                               { $$ = new AstNew{$1,  nullptr}; }
        |       yNEW__ETC expr                          { $$ = new AstNewCopy{$1, $2}; }
        |       yNEW__PAREN '(' list_of_argumentsE ')'  { $$ = new AstNew{$1, $3}; }
        ;

dynamic_array_new:   // ==IEEE: dynamic_array_new
                yNEW__ETC '[' expr ']'                  { $$ = new AstNewDynamic{$1, $3, nullptr}; }
        |       yNEW__ETC '[' expr ']' '(' expr ')'     { $$ = new AstNewDynamic{$1, $3, $6}; }
        ;

//************************************************
// Case/If

unique_priorityE:    // IEEE: unique_priority + empty
                /*empty*/                               { $$ = uniq_NONE; }
        |       yPRIORITY                               { $$ = uniq_PRIORITY; }
        |       yUNIQUE                                 { $$ = uniq_UNIQUE; }
        |       yUNIQUE0                                { $$ = uniq_UNIQUE0; }
        ;

caseStart:               // IEEE: part of case_statement
                yCASE  '(' exprTypeCompare ')'
                        { $$ = GRAMMARP->m_caseAttrp = new AstCase{$1, VCaseType::CT_CASE, $3, nullptr}; }
        |       yCASEX '(' exprTypeCompare ')'
                        { $$ = GRAMMARP->m_caseAttrp = new AstCase{$1, VCaseType::CT_CASEX, $3, nullptr}; }
        |       yCASEZ '(' exprTypeCompare ')'
                        { $$ = GRAMMARP->m_caseAttrp = new AstCase{$1, VCaseType::CT_CASEZ, $3, nullptr}; }
        ;

caseAttrE:
                /*empty*/                               { }
        |       caseAttrE yVL_FULL_CASE                 { GRAMMARP->m_caseAttrp->fullPragma(true); }
        |       caseAttrE yVL_PARALLEL_CASE             { GRAMMARP->m_caseAttrp->parallelPragma(true); }
        ;

case_itemList:       // IEEE: { case_item + ... }
                caseCondList colon stmt                    { $$ = new AstCaseItem{$2, $1, $3}; }
        |       yDEFAULT colon stmt                        { $$ = new AstCaseItem{$1, nullptr, $3}; }
        |       yDEFAULT stmt                              { $$ = new AstCaseItem{$1, nullptr, $2}; }
        |       case_itemList caseCondList colon stmt      { $$ = $1->addNext(new AstCaseItem{$3, $2, $4}); }
        |       case_itemList yDEFAULT stmt                { $$ = $1->addNext(new AstCaseItem{$2, nullptr, $3}); }
        |       case_itemList yDEFAULT colon stmt          { $$ = $1->addNext(new AstCaseItem{$2, nullptr, $4}); }
        ;

case_inside_itemList:        // IEEE: { case_inside_item + range_list ... }
                range_list colon stmt                      { $$ = new AstCaseItem{$2, $1, $3}; }
        |       yDEFAULT colon stmt                        { $$ = new AstCaseItem{$1, nullptr, $3}; }
        |       yDEFAULT stmt                              { $$ = new AstCaseItem{$1, nullptr, $2}; }
        |       case_inside_itemList range_list colon stmt { $$ = $1->addNext(new AstCaseItem{$3, $2, $4}); }
        |       case_inside_itemList yDEFAULT stmt         { $$ = $1->addNext(new AstCaseItem{$2, nullptr, $3}); }
        |       case_inside_itemList yDEFAULT colon stmt   { $$ = $1->addNext(new AstCaseItem{$2, nullptr, $4}); }
        ;

rand_case_itemList:       // IEEE: { rand_case_item + ... }
        //                      // Randcase syntax doesn't have default, or expression lists
                expr colon stmt                            { $$ = new AstCaseItem{$2, $1, $3}; }
        |       rand_case_itemList expr colon stmt         { $$ = $1->addNext(new AstCaseItem{$3, $2, $4}); }
        ;

range_list:     // ==IEEE: range_list/open_range_list + value_range/open_value_range
                value_range                             { $$ = $1; }
        |       range_list ',' value_range              { $$ = $1->addNext($3); }
        ;

value_range:         // ==IEEE: value_range/open_value_range
                expr                                    { $$ = $1; }
        |       '[' expr ':' expr ']'                   { $$ = new AstInsideRange{$1, $2, $4}; }
        //                      // IEEE-2023: added all four:
        //                      // Skipped as '$' is part of our expr
        //                      // IEEE-2023: '[' '$' ':' expr ']'
        //                      // Skipped as '$' is part of our expr
        //                      // IEEE-2023: '[' expr ':' '$' ']'
        |       '[' expr yP_PLUSSLASHMINUS expr ']'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: +/- range"); DEL($2, $4); }
        |       '[' expr yP_PLUSPCTMINUS expr ']'
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: +%- range"); DEL($2, $4); }
        ;

covergroup_value_range:  // ==IEEE-2012: covergroup_value_range
                cgexpr                                  { $$ = $1; }
        |       '[' cgexpr ':' cgexpr ']'
                        { $$ = nullptr; BBCOVERIGN($1, "Ignoring unsupported: covergroup value range"); DEL($2, $4); }
        //                      // IEEE-2023: added all four:
        //                      // Skipped as '$' is part of our expr
        //                      // IEEE-2023: '[' '$' ':' cgexpr ']'
        //                      // Skipped as '$' is part of our expr
        //                      // IEEE-2023: '[' cgexpr ':' '$' ']'
        |       '[' cgexpr yP_PLUSSLASHMINUS cgexpr ']'
                        { $$ = nullptr; BBCOVERIGN($1, "Ignoring unsupported: covergroup value range"); DEL($2, $4); }
        |       '[' cgexpr yP_PLUSPCTMINUS cgexpr ']'
                        { $$ = nullptr; BBCOVERIGN($1, "Ignoring unsupported: covergroup value range"); DEL($2, $4); }
        ;

caseCondList:        // IEEE: part of case_item
                exprTypeCompare                         { $$ = $1; }
        |       caseCondList ',' exprTypeCompare        { $$ = $1->addNext($3); }
        ;

patternNoExpr:           // IEEE: pattern **Excluding Expr*
                '.' idAny/*variable*/
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: '{} tagged patterns"); }
        |       yP_DOTSTAR
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: '{} tagged patterns"); }
        //                      // IEEE: "expr" excluded; expand in callers
        //                      // "yTAGGED idAny [expr]" Already part of expr
        |       yTAGGED idAny/*member_identifier*/ patternNoExpr
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: '{} tagged patterns"); DEL($3); }
        //                      // "yP_TICKBRA patternList '}'" part of expr under assignment_pattern
        ;

patternList:             // IEEE: part of pattern
                patternOne                              { $$ = $1; }
        |       patternList ',' patternOne              { $$ = addNextNull($1, $3); }
        ;

patternOne:              // IEEE: part of pattern
                expr
                        { if ($1) $$ = new AstPatMember{$1->fileline(), $1, nullptr, nullptr}; else $$ = nullptr; }
        |       expr '{' argsExprList '}'               { $$ = new AstPatMember{$2, $3, nullptr, $1}; }
        |       patternNoExpr                           { $$ = $1; }
        ;

patternMemberList:       // IEEE: part of pattern and assignment_pattern
                patternMemberOne                        { $$ = $1; }
        |       patternMemberList ',' patternMemberOne  { $$ = addNextNull($1, $3); }
        ;

patternMemberOne:   // IEEE: part of pattern and assignment_pattern
                patternKey ':' expr                     { $$ = new AstPatMember{$1->fileline(), $3, $1, nullptr}; }
        |       patternKey ':' patternNoExpr            { $$ = nullptr; BBUNSUP($2, "Unsupported: '{} .* patterns"); DEL($1, $3); }
        //                      // From assignment_pattern_key
        |       yDEFAULT ':' expr                       { $$ = new AstPatMember{$1, $3, nullptr, nullptr}; $$->isDefault(true); }
        |       yDEFAULT ':' patternNoExpr              { $$ = nullptr; BBUNSUP($2, "Unsupported: '{} .* patterns"); DEL($3); }
        ;

patternKey:              // IEEE: merge structure_pattern_key, array_pattern_key, assignment_pattern_key
        //                      // IEEE: structure_pattern_key
        //                      // id/*member*/ is part of constExpr below
        //UNSUP constExpr                               { $$ = $1; }
        //                      // IEEE: assignment_pattern_key
        //                      // Verilator:
        //                      //   The above expressions cause problems because "foo" may be
        //                      //   a constant identifier (if array) or a reference to the
        //                      //   "foo"member (if structure)
        //                      //   So for now we only allow a true constant number, or an
        //                      //   identifier which we treat as a structure member name
                yaINTNUM
                        { $$ = new AstConst{$<fl>1, *$1}; }
        |       '-' yaINTNUM
                        { V3Number neg{*$2}; neg.opNegate(*$2); $$ = new AstConst{$<fl>2, neg}; }
        |       yaFLOATNUM
                        { $$ = new AstConst{$<fl>1, AstConst::RealDouble{}, $1}; }
        |       id
                        { $$ = new AstText{$<fl>1, *$1}; }
        |       strAsInt
                        { $$ = $1; }
        |       simple_typeNoRef
                        { $$ = $1; }
        //                      // expanded from simple_type ps_type_identifier (part of simple_type)
        //                      // expanded from simple_type ps_parameter_identifier (part of simple_type)
        |       packageClassScope id
                        { $$ = AstDot::newIfPkg($<fl>1, $1,
                                                new AstParseRef{$<fl>2, *$2, nullptr, nullptr}); }
        |       packageClassScopeE idType
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, nullptr};
                          $$ = refp; }
        ;

assignment_pattern:   // ==IEEE: assignment_pattern
        // This doesn't match the text of the spec.  I think a : is missing, or example code needed
        // yP_TICKBRA constExpr exprList '}'    { $$="'{"+$2+" "+$3"}"; }
        //                      // "'{ const_expression }" is same as patternList with one entry
        //                      // From patternNoExpr
        //                      // also IEEE: "''{' expression { ',' expression } '}'"
        //                      //      matches since patternList includes expr
                yP_TICKBRA patternList '}'              { $$ = new AstPattern{$1, $2}; }
        //                      // From patternNoExpr
        //                      // also IEEE "''{' structure_pattern_key ':' ...
        //                      // also IEEE "''{' array_pattern_key ':' ...
        |       yP_TICKBRA patternMemberList '}'        { $$ = new AstPattern{$1, $2}; }
        //                      // IEEE: Not in grammar, but in VMM
        |       yP_TICKBRA '}'                          { $$ = new AstPattern{$1, nullptr}; }
        ;

// "datatype id = x {, id = x }"  |  "yaId = x {, id=x}" is legal
for_initializationE:      // ==IEEE: for_initialization + for_variable_declaration
                /* empty */                     { $$ = nullptr; }
        |       for_initializationItemList      { $$ = $1; }
        ;

for_initializationItemList:      // IEEE: [for_variable_declaration...]
                for_initializationItem                  { $$ = $1; }
        |       for_initializationItemList ',' for_initializationItem   { $$ = addNextNull($1, $3); }
        ;

for_initializationItem:          // IEEE: variable_assignment + for_variable_declaration
        //                      // IEEE: for_variable_declaration
                data_type idAny/*new*/ '=' expr
                        { VARRESET_NONLIST(VAR); VARDTYPE($1);
                          AstVar* const varp = VARDONEA($<fl>2, *$2, nullptr, nullptr);
                          varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                          $$ = varp;
                          $$->addNext(new AstAssign{$3, new AstParseRef{$<fl>2, *$2}, $4}); }
        //                      // IEEE-2012:
        |       yVAR data_type idAny/*new*/ '=' expr
                        { VARRESET_NONLIST(VAR); VARDTYPE($2);
                          AstVar* const varp = VARDONEA($<fl>3, *$3, nullptr, nullptr);
                          varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                          $$ = varp;
                          $$->addNext(new AstAssign{$4, new AstParseRef{$<fl>3, *$3}, $5}); }
        //                      // IEEE: variable_assignment
        //                      // UNSUP variable_lvalue below
        |       id/*newOrExisting*/ '=' expr
                        { if (GRAMMARP->m_varDecl) {
                              AstVar* const varp = VARDONEA($<fl>1, *$1, nullptr, nullptr);
                              varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                              $$ = varp;
                              $$->addNext(new AstAssign{$2, new AstParseRef{$<fl>1, *$1}, $3});
                          } else {
                              $$ = new AstAssign{$2, new AstParseRef{$<fl>1, *$1}, $3};
                          }
                        }
        ;

for_stepE:               // IEEE: for_step + empty
                /* empty */                             { $$ = nullptr; }
        |       for_step                                { $$ = $1; }
        ;

for_step:                // IEEE: for_step
                for_step_assignment                     { $$ = $1; }
        |       for_step ',' for_step_assignment        { $$ = addNextNull($1, $3); }
        ;

for_step_assignment:     // ==IEEE: for_step_assignment
                foperator_assignment                    { $$ = $1; }
        |       finc_or_dec_expression                  { $$ = new AstStmtExpr{$<fl>1, $1}; }
        //                      // IEEE: function_subroutine_call
        |       task_subroutine_callNoSemi              { $$ = $1; }
        ;

loop_variables:          // IEEE: loop_variables
                loop_variableE                          { $$ = $1; }
        |       loop_variables ',' loop_variableE       { $$ = $1->addNext($3); }
        ;

loop_variableE:          // IEEE: part of loop_variables
                /* empty */                             { $$ = new AstEmpty{CRELINE()}; }
        |       parseRefBase                            { $$ = $1; }
        ;

//************************************************
// Functions/tasks

taskRef:            // IEEE: part of tf_call
                id                                      { $$ = new AstTaskRef{$<fl>1, *$1, nullptr}; }
        |       id '(' list_of_argumentsE ')'           { $$ = new AstTaskRef{$<fl>1, *$1, $3}; }
        |       packageClassScope id '(' list_of_argumentsE ')'
                        { $$ = AstDot::newIfPkg($<fl>2, $1, new AstTaskRef{$<fl>2, *$2, $4}); }
        ;

funcRef:             // IEEE: part of tf_call
        //                      // package_scope/hierarchical_... is part of expr, so just need ID
        //                      //      making-a                id-is-a
        //                      //      -----------------       ------------------
        //                      //      tf_call                 tf_identifier           expr (list_of_arguments)
        //                      //      method_call(post .)     function_identifier     expr (list_of_arguments)
        //                      //      property_instance       property_identifier     property_actual_arg
        //                      //      sequence_instance       sequence_identifier     sequence_actual_arg
        //                      //      let_expression          let_identifier          let_actual_arg
        //
                id '(' list_of_argumentsE ')'
                        { $$ = new AstFuncRef{$<fl>1, *$1, $3}; }
        |       packageClassScope id '(' list_of_argumentsE ')'
                        { $$ = AstDot::newIfPkg($<fl>2, $1, new AstFuncRef{$<fl>2, *$2, $4}); }
        //UNSUP list_of_argumentE should be pev_list_of_argumentE
        //UNSUP: idDottedSel is really just id to allow dotted method calls
        ;

task_subroutine_callNoSemi:  // similar to IEEE task_subroutine_call but without ';'
        //                      // Expr included here to resolve our not knowing what is a method call
        //                      // Expr here must result in a subroutine_call
                task_subroutine_callNoMethod            { $$ = $1->makeStmt(); }
        |       fexpr '.' task_subroutine_callNoMethod  { $$ = (new AstDot{$<fl>2, false, $1, $3})->makeStmt(); }
        |       system_t_stmt_call                      { $$ = $1; }
        //                      // Any system function as a task
        |       system_f_or_t_expr_call                 { $$ = new AstStmtExpr{$<fl>1, $1}; }
        //                      // Not here in IEEE; from class_constructor_declaration
        //                      // Because we've joined class_constructor_declaration into generic functions
        //                      // Way over-permissive;
        //                      // IEEE: [ ySUPER '.' yNEW [ '(' list_of_arguments ')' ] ';' ]
        |       fexpr '.' class_newNoScope              { $$ = (new AstDot{$<fl>2, false, $1, $3})->makeStmt(); }
        ;

task_subroutine_callNoMethod:    // function_subroutine_callNoMethod (as task)
        //                      // IEEE: tf_call
                taskRef                                 { $$ = $1; }
        //                      // funcref below not task ref to avoid conflict, must later handle either
        |       funcRef yWITH__PAREN '(' expr ')'       { $$ = new AstWithParse{$2, $1, $4}; }
        //                      // can call as method and yWITH without parenthesis
        |       id yWITH__PAREN '(' expr ')'            { $$ = new AstWithParse{$2, new AstFuncRef{$<fl>1, *$1, nullptr}, $4}; }
        //                      // IEEE: method_call requires a "." so is in expr
        //                      // IEEE: ['std::'] not needed, as normal std package resolution will find it
        //                      // IEEE: randomize_call
        //                      // We implement randomize as a normal funcRef, since randomize isn't a keyword
        //                      // Note yNULL is already part of expressions, so they come for free
        |       funcRef yWITH__CUR constraint_block     { $$ = new AstWithParse{$2, $1, nullptr, $3}; }
        |       funcRef yWITH__PAREN_CUR '(' expr ')' constraint_block   { $$ = new AstWithParse{$2, $1, $4, $6}; }
        ;

function_subroutine_callNoMethod:        // IEEE: function_subroutine_call (as function)
        //                      // IEEE: tf_call
                funcRef                                 { $$ = $1; }
        |       funcRef yWITH__PAREN '(' expr ')'       { $$ = new AstWithParse{$2, $1, $4}; }
        //                      // can call as method and yWITH without parenthesis
        |       id yWITH__PAREN '(' expr ')'            { $$ = new AstWithParse{$2, new AstFuncRef{$<fl>1, *$1, nullptr}, $4}; }
        |       system_f_only_expr_call                 { $$ = $1; }
        |       system_f_or_t_expr_call                 { $$ = $1; }
        //                      // IEEE: method_call requires a "." so is in expr
        //                      // IEEE: ['std::'] not needed, as normal std package resolution will find it
        //                      // IEEE: randomize_call
        //                      // We implement randomize as a normal funcRef, since randomize isn't a keyword
        //                      // Note yNULL is already part of expressions, so they come for free
        |       funcRef yWITH__CUR constraint_block     { $$ = new AstWithParse{$2, $1, nullptr, $3}; }
        |       funcRef yWITH__PAREN_CUR '(' expr ')' constraint_block   { $$ = new AstWithParse{$2, $1, $4, $6}; }
        ;

system_t_stmt_call:  // IEEE: part of system_tf_call (as task returning statement)
        //
                yaD_PLI systemDpiArgsE                  { AstTaskRef* const refp = new AstTaskRef{$<fl>1, *$1, $2};
                                                          refp->pli(true);
                                                          $$ = refp->makeStmt(); }
        //
        |       yD_DUMPPORTS '(' idDottedSel ',' expr ')'  { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::FILE, $5}; DEL($3);
                                                          $$->addNext(new AstDumpCtl{$<fl>1, VDumpCtlType::VARS,
                                                                                     new AstConst{$<fl>1, 1}}); }
        |       yD_DUMPPORTS '(' ',' expr ')'           { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::FILE, $4};
                                                          $$->addNext(new AstDumpCtl{$<fl>1, VDumpCtlType::VARS,
                                                                                     new AstConst{$<fl>1, 1}}); }
        |       yD_DUMPFILE '(' expr ')'                { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::FILE, $3}; }
        |       yD_DUMPVARS parenE                      { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::VARS,
                                                                              new AstConst{$<fl>1, 0}}; }
        |       yD_DUMPVARS '(' expr ')'                { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::VARS, $3}; }
        |       yD_DUMPVARS '(' expr ',' exprList ')'   { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::VARS, $3}; DEL($5); }
        |       yD_DUMPALL parenE                       { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::ALL}; }
        |       yD_DUMPALL '(' expr ')'                 { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::ALL}; DEL($3); }
        |       yD_DUMPFLUSH parenE                     { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::FLUSH}; }
        |       yD_DUMPFLUSH '(' expr ')'               { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::FLUSH}; DEL($3); }
        |       yD_DUMPLIMIT '(' expr ')'               { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::LIMIT, $3}; }
        |       yD_DUMPLIMIT '(' expr ',' expr ')'      { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::LIMIT, $3}; DEL($5); }
        |       yD_DUMPOFF parenE                       { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::OFF}; }
        |       yD_DUMPOFF '(' expr ')'                 { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::OFF}; DEL($3); }
        |       yD_DUMPON parenE                        { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::ON}; }
        |       yD_DUMPON '(' expr ')'                  { $$ = new AstDumpCtl{$<fl>1, VDumpCtlType::ON}; DEL($3); }
        //
        |       yD_C '(' cStrList ')' {
                    AstCStmtUser* cstmtp = nullptr;
                    if (!v3Global.opt.ignc()) {
                        cstmtp = new AstCStmtUser{$1, true};
                        cstmtp->add($3);
                    }
                    $$ = cstmtp;
                }
        |       yD_SDF_ANNOTATE '(' exprEListE ')'      { $$ = nullptr; $1->v3warn(SPECIFYIGN, "Ignoring unsupported: $sdf_annotate"); DEL($3); }
        |       yD_STACKTRACE parenE                    { $$ = new AstStackTraceT{$1}; }
        |       yD_SYSTEM '(' expr ')'                  { $$ = new AstSystemT{$1, $3}; }
        //
        |       yD_EXIT parenE                          { $$ = new AstFinish{$1}; }
        //
        |       yD_FCLOSE '(' expr ')'                  { $$ = new AstFClose{$1, $3}; }
        |       yD_FFLUSH parenE                        { $$ = new AstFFlush{$1, nullptr}; }
        |       yD_FFLUSH '(' expr ')'                  { $$ = new AstFFlush{$1, $3}; }
        |       yD_FINISH parenE                        { $$ = new AstFinish{$1}; }
        |       yD_FINISH '(' expr ')'                  { $$ = new AstFinish{$1}; DEL($3); }
        |       yD_STOP parenE                          { $$ = new AstStop{$1, false}; }
        |       yD_STOP '(' expr ')'                    { $$ = new AstStop{$1, false}; DEL($3); }
        //
        |       yD_SFORMAT '(' expr ',' exprDispList ')'        { $$ = new AstSFormat{$1, $3, $5}; }
        |       yD_SWRITE  '(' expr ',' exprDispList ')'        { $$ = new AstSFormat{$1, $3, $5}; }
        |       yD_SWRITEB '(' expr ',' exprDispList ')'        { $$ = new AstSFormat{$1, $3, $5, 'b'}; }
        |       yD_SWRITEH '(' expr ',' exprDispList ')'        { $$ = new AstSFormat{$1, $3, $5, 'h'}; }
        |       yD_SWRITEO '(' expr ',' exprDispList ')'        { $$ = new AstSFormat{$1, $3, $5, 'o'}; }
        //
        |       yD_DISPLAY parenE                               { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, nullptr}; }
        |       yD_DISPLAY '(' commasE exprDispList ')'         { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, $4}; }
        |       yD_DISPLAYB parenE                              { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, nullptr, 'b'}; }
        |       yD_DISPLAYB '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, $4, 'b'}; }
        |       yD_DISPLAYH parenE                              { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, nullptr, 'h'}; }
        |       yD_DISPLAYH '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, $4, 'h'}; }
        |       yD_DISPLAYO parenE                              { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, nullptr, 'o'}; }
        |       yD_DISPLAYO '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, nullptr, $4, 'o'}; }
        |       yD_MONITOR  '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, nullptr, $4}; }
        |       yD_MONITORB '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, nullptr, $4, 'b'}; }
        |       yD_MONITORH '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, nullptr, $4, 'h'}; }
        |       yD_MONITORO '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, nullptr, $4, 'o'}; }
        |       yD_STROBE   '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, nullptr, $4}; }
        |       yD_STROBEB  '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, nullptr, $4, 'b'}; }
        |       yD_STROBEH  '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, nullptr, $4, 'h'}; }
        |       yD_STROBEO  '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, nullptr, $4, 'o'}; }
        |       yD_WRITE    parenE                              { $$ = nullptr; }  // NOP
        |       yD_WRITE    '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, nullptr, $4}; }
        |       yD_WRITEB   parenE                              { $$ = nullptr; }  // NOP
        |       yD_WRITEB   '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, nullptr, $4, 'b'}; }
        |       yD_WRITEH   parenE                              { $$ = nullptr; }  // NOP
        |       yD_WRITEH   '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, nullptr, $4, 'h'}; }
        |       yD_WRITEO   parenE                              { $$ = nullptr; }  // NOP
        |       yD_WRITEO   '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, nullptr, $4, 'o'}; }
        |       yD_FDISPLAY '(' expr ')'                        { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, nullptr}; }
        |       yD_FDISPLAY '(' expr ',' exprDispList ')'       { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, $5}; }
        |       yD_FDISPLAYB '(' expr ')'                       { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, nullptr, 'b'}; }
        |       yD_FDISPLAYB '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, $5, 'b'}; }
        |       yD_FDISPLAYH '(' expr ')'                       { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, nullptr, 'h'}; }
        |       yD_FDISPLAYH '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, $5, 'h'}; }
        |       yD_FDISPLAYO '(' expr ')'                       { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, nullptr, 'o'}; }
        |       yD_FDISPLAYO '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_DISPLAY, $3, $5, 'o'}; }
        |       yD_FMONITOR  '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, $3, $5}; }
        |       yD_FMONITORB '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, $3, $5, 'b'}; }
        |       yD_FMONITORH '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, $3, $5, 'h'}; }
        |       yD_FMONITORO '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_MONITOR, $3, $5, 'o'}; }
        |       yD_FSTROBE   '(' expr ')'                       { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, $3, nullptr}; }
        |       yD_FSTROBE   '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, $3, $5}; }
        |       yD_FSTROBEB  '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, $3, $5, 'b'}; }
        |       yD_FSTROBEH  '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, $3, $5, 'h'}; }
        |       yD_FSTROBEO  '(' expr ',' exprDispList ')'      { $$ = new AstDisplay{$1, VDisplayType::DT_STROBE, $3, $5, 'o'}; }
        |       yD_FWRITE   '(' expr ')'                        { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, $3, nullptr}; }
        |       yD_FWRITE   '(' expr ',' exprDispList ')'       { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, $3, $5}; }
        |       yD_FWRITEB  '(' expr ',' exprDispList ')'       { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, $3, $5, 'b'}; }
        |       yD_FWRITEH  '(' expr ',' exprDispList ')'       { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, $3, $5, 'h'}; }
        |       yD_FWRITEO  '(' expr ',' exprDispList ')'       { $$ = new AstDisplay{$1, VDisplayType::DT_WRITE, $3, $5, 'o'}; }
        |       yD_INFO     parenE                              { $$ = new AstDisplay{$1, VDisplayType::DT_INFO, nullptr, nullptr}; }
        |       yD_INFO     '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_INFO, nullptr, $4}; }
        |       yD_WARNING  parenE                              { $$ = new AstDisplay{$1, VDisplayType::DT_WARNING, nullptr, nullptr}; }
        |       yD_WARNING  '(' commasE exprDispList ')'        { $$ = new AstDisplay{$1, VDisplayType::DT_WARNING, nullptr, $4}; }
        |       yD_ERROR    parenE                              { $$ = GRAMMARP->createDisplayError($1); }
        |       yD_ERROR    '(' commasE exprDispList ')'
                        { $$ = new AstDisplay{$1, VDisplayType::DT_ERROR, nullptr, $4};
                          $$->addNext(new AstStop{$1, false}); }
        |       yD_FATAL    parenE
                        { $$ = new AstDisplay{$1, VDisplayType::DT_FATAL, nullptr, nullptr};
                          $$->addNext(new AstStop{$1, true}); }
        |       yD_FATAL    '(' expr ')'
                        { $$ = new AstDisplay{$1, VDisplayType::DT_FATAL, nullptr, nullptr};
                          $$->addNext(new AstStop{$1, true}); DEL($3); }
        |       yD_FATAL    '(' expr ',' exprDispList ')'
                        { $$ = new AstDisplay{$1, VDisplayType::DT_FATAL, nullptr, $5};
                          $$->addNext(new AstStop{$1, true}); DEL($3); }
        //
        |       yD_ASSERTCTL '(' expr ')'                                            { $$ = new AstAssertCtl{$1, $3}; }
        |       yD_ASSERTCTL '(' expr ',' exprE ')'                                  { $$ = new AstAssertCtl{$1, $3, $5}; }
        |       yD_ASSERTCTL '(' expr ',' exprE ',' exprE ')'                        { $$ = new AstAssertCtl{$1, $3, $5, $7}; }
        |       yD_ASSERTCTL '(' expr ',' exprE ',' exprE ',' exprE ')'              { $$ = new AstAssertCtl{$1, $3, $5, $7, $9}; }
        |       yD_ASSERTCTL '(' expr ',' exprE ',' exprE ',' exprE ',' exprList ')' { $$ = new AstAssertCtl{$1, $3, $5, $7, $9, $11}; }
        |       yD_ASSERTFAILOFF '(' expr ')'                   { $$ = new AstAssertCtl{$1, VAssertCtlType::FAIL_OFF, 31, 7, $3}; }
        |       yD_ASSERTFAILOFF '(' exprE ',' exprList ')'     { $$ = new AstAssertCtl{$1, VAssertCtlType::FAIL_OFF, 31, 7, $3, $5}; }
        |       yD_ASSERTFAILOFF parenE                         { $$ = new AstAssertCtl{$1, VAssertCtlType::FAIL_OFF, 31, 7}; }
        |       yD_ASSERTFAILON '(' expr ')'                    { $$ = new AstAssertCtl{$1, VAssertCtlType::FAIL_ON, 31, 7, $3}; }
        |       yD_ASSERTFAILON '(' exprE ',' exprList ')'      { $$ = new AstAssertCtl{$1, VAssertCtlType::FAIL_ON, 31, 7, $3, $5}; }
        |       yD_ASSERTFAILON parenE                          { $$ = new AstAssertCtl{$1, VAssertCtlType::FAIL_ON, 31, 7}; }
        |       yD_ASSERTKILL '(' expr ')'                      { $$ = new AstAssertCtl{$1, VAssertCtlType::KILL, 15, 7, $3}; }
        |       yD_ASSERTKILL '(' exprE ',' exprList ')'        { $$ = new AstAssertCtl{$1, VAssertCtlType::KILL, 15, 7, $3, $5}; }
        |       yD_ASSERTKILL parenE                            { $$ = new AstAssertCtl{$1, VAssertCtlType::KILL, 15, 7}; }
        |       yD_ASSERTNONVACUOUSON '(' expr ')'                 { $$ = new AstAssertCtl{$1, VAssertCtlType::NONVACUOUS_ON, 31, 7, $3}; }
        |       yD_ASSERTNONVACUOUSON '(' exprE ',' exprList ')'   { $$ = new AstAssertCtl{$1, VAssertCtlType::NONVACUOUS_ON, 31, 7, $3, $5}; }
        |       yD_ASSERTNONVACUOUSON parenE                       { $$ = new AstAssertCtl{$1, VAssertCtlType::NONVACUOUS_ON, 31, 7}; }
        |       yD_ASSERTOFF '(' expr ')'                       { $$ = new AstAssertCtl{$1, VAssertCtlType::OFF, 15, 7, $3}; }
        |       yD_ASSERTOFF '(' exprE ',' exprList ')'         { $$ = new AstAssertCtl{$1, VAssertCtlType::OFF, 15, 7, $3, $5}; }
        |       yD_ASSERTOFF parenE                             { $$ = new AstAssertCtl{$1, VAssertCtlType::OFF, 15, 7}; }
        |       yD_ASSERTON '(' expr ')'                        { $$ = new AstAssertCtl{$1, VAssertCtlType::ON, 15, 7, $3}; }
        |       yD_ASSERTON '(' exprE ',' exprList ')'          { $$ = new AstAssertCtl{$1, VAssertCtlType::ON, 15, 7, $3, $5}; }
        |       yD_ASSERTON parenE                              { $$ = new AstAssertCtl{$1, VAssertCtlType::ON, 15, 7}; }
        |       yD_ASSERTPASSOFF '(' expr ')'                   { $$ = new AstAssertCtl{$1, VAssertCtlType::PASS_OFF, 31, 7, $3}; }
        |       yD_ASSERTPASSOFF '(' exprE ',' exprList ')'     { $$ = new AstAssertCtl{$1, VAssertCtlType::PASS_OFF, 31, 7, $3, $5}; }
        |       yD_ASSERTPASSOFF parenE                         { $$ = new AstAssertCtl{$1, VAssertCtlType::PASS_OFF, 31, 7}; }
        |       yD_ASSERTPASSON '(' expr ')'                    { $$ = new AstAssertCtl{$1, VAssertCtlType::PASS_ON, 31, 7, $3}; }
        |       yD_ASSERTPASSON '(' exprE ',' exprList ')'      { $$ = new AstAssertCtl{$1, VAssertCtlType::PASS_ON, 31, 7, $3, $5}; }
        |       yD_ASSERTPASSON parenE                          { $$ = new AstAssertCtl{$1, VAssertCtlType::PASS_ON, 31, 7}; }
        |       yD_ASSERTVACUOUSOFF '(' expr ')'                { $$ = new AstAssertCtl{$1, VAssertCtlType::VACUOUS_OFF, 31, 7, $3}; }
        |       yD_ASSERTVACUOUSOFF '(' exprE ',' exprList ')'  { $$ = new AstAssertCtl{$1, VAssertCtlType::VACUOUS_OFF, 31, 7, $3, $5}; }
        |       yD_ASSERTVACUOUSOFF parenE                      { $$ = new AstAssertCtl{$1, VAssertCtlType::VACUOUS_OFF, 31, 7}; }
        //
        |       yD_MONITOROFF parenE                    { $$ = new AstMonitorOff{$1, true}; }
        |       yD_MONITORON parenE                     { $$ = new AstMonitorOff{$1, false}; }
        //
        |       yD_PRINTTIMESCALE                       { $$ = new AstPrintTimeScale{$1}; }
        |       yD_PRINTTIMESCALE '(' ')'               { $$ = new AstPrintTimeScale{$1}; }
        |       yD_PRINTTIMESCALE '(' idClassSel ')'    { $$ = new AstPrintTimeScale{$1}; DEL($3); }
        |       yD_TIMEFORMAT '(' exprE ',' exprE ',' exprE ',' exprE ')'
                        { $$ = new AstTimeFormat{$1, $3, $5, $7, $9}; }
        |       yD_TIMEFORMAT '(' exprE ',' exprE ',' exprE ')'
                        { $$ = new AstTimeFormat{$1, $3, $5, $7, nullptr}; }
        |       yD_TIMEFORMAT '(' exprE ',' exprE ')'
                        { $$ = new AstTimeFormat{$1, $3, $5, nullptr, nullptr}; }
        |       yD_TIMEFORMAT '(' exprE ')'
                        { $$ = new AstTimeFormat{$1, $3, nullptr, nullptr, nullptr}; }
        //
        |       yD_READMEMB '(' expr ',' idClassSel ')'                         { $$ = new AstReadMem{$1, false, $3, $5, nullptr, nullptr}; }
        |       yD_READMEMB '(' expr ',' idClassSel ',' expr ')'                { $$ = new AstReadMem{$1, false, $3, $5, $7, nullptr}; }
        |       yD_READMEMB '(' expr ',' idClassSel ',' expr ',' expr ')'       { $$ = new AstReadMem{$1, false, $3, $5, $7, $9}; }
        |       yD_READMEMH '(' expr ',' idClassSel ')'                         { $$ = new AstReadMem{$1, true,  $3, $5, nullptr, nullptr}; }
        |       yD_READMEMH '(' expr ',' idClassSel ',' expr ')'                { $$ = new AstReadMem{$1, true,  $3, $5, $7, nullptr}; }
        |       yD_READMEMH '(' expr ',' idClassSel ',' expr ',' expr ')'       { $$ = new AstReadMem{$1, true,  $3, $5, $7, $9}; }
        //
        |       yD_WRITEMEMB '(' expr ',' idClassSel ')'                        { $$ = new AstWriteMem{$1, false, $3, $5, nullptr, nullptr}; }
        |       yD_WRITEMEMB '(' expr ',' idClassSel ',' expr ')'               { $$ = new AstWriteMem{$1, false, $3, $5, $7, nullptr}; }
        |       yD_WRITEMEMB '(' expr ',' idClassSel ',' expr ',' expr ')'      { $$ = new AstWriteMem{$1, false, $3, $5, $7, $9}; }
        |       yD_WRITEMEMH '(' expr ',' idClassSel ')'                        { $$ = new AstWriteMem{$1, true,  $3, $5, nullptr, nullptr}; }
        |       yD_WRITEMEMH '(' expr ',' idClassSel ',' expr ')'               { $$ = new AstWriteMem{$1, true,  $3, $5, $7, nullptr}; }
        |       yD_WRITEMEMH '(' expr ',' idClassSel ',' expr ',' expr ')'      { $$ = new AstWriteMem{$1, true,  $3, $5, $7, $9}; }
        //
        |       yD_CAST '(' expr ',' expr ')'
                        { FileLine* const fl_nowarn = new FileLine{$1};
                          fl_nowarn->warnOff(V3ErrorCode::WIDTH, true);
                          $$ = new AstAssertIntrinsic{fl_nowarn, new AstCastDynamic{fl_nowarn, $5, $3},
                                                      nullptr, nullptr}; }
        ;

system_f_only_expr_call:  // IEEE: part of system_tf_call (for functions returning expressions)
                yaD_PLI systemDpiArgsE                  { $$ = new AstFuncRef{$<fl>1, *$1, $2}; VN_CAST($$, FuncRef)->pli(true); }
        //
        |       yD_C '(' cStrList ')' {
                    AstCExprUser* cexprp = nullptr;
                    if (!v3Global.opt.ignc()) {
                        cexprp = new AstCExprUser{$1};
                        cexprp->add($3);
                    }
                    $$ = cexprp;
                }
        |       yD_CPURE '(' cStrList ')' {
                    AstCExprUser* cexprp = nullptr;
                    if (!v3Global.opt.ignc()) {
                        cexprp = new AstCExprUser{$1, AstCExprUser::Pure{}};
                        cexprp->add($3);
                    }
                    $$ = cexprp;
                }
        |       yD_CAST '(' expr ',' expr ')'           { $$ = new AstCastDynamic{$1, $5, $3}; }
        |       yD_STACKTRACE parenE                    { $$ = new AstStackTraceF{$1}; }
        |       yD_SYSTEM  '(' expr ')'                 { $$ = new AstSystemF{$1, $3}; }
        ;

system_f_or_t_expr_call:  // IEEE: part of system_tf_call (can be task or func)
                yD_ACOS '(' expr ')'                    { $$ = new AstAcosD{$1, $3}; }
        |       yD_ACOSH '(' expr ')'                   { $$ = new AstAcoshD{$1, $3}; }
        |       yD_ASIN '(' expr ')'                    { $$ = new AstAsinD{$1, $3}; }
        |       yD_ASINH '(' expr ')'                   { $$ = new AstAsinhD{$1, $3}; }
        |       yD_ATAN '(' expr ')'                    { $$ = new AstAtanD{$1, $3}; }
        |       yD_ATAN2 '(' expr ',' expr ')'          { $$ = new AstAtan2D{$1, $3, $5}; }
        |       yD_ATANH '(' expr ')'                   { $$ = new AstAtanhD{$1, $3}; }
        |       yD_BITS '(' exprOrDataType ')'          { $$ = new AstAttrOf{$1, VAttrType::DIM_BITS, $3}; }
        |       yD_BITS '(' exprOrDataType ',' expr ')' { $$ = new AstAttrOf{$1, VAttrType::DIM_BITS, $3, $5}; }
        |       yD_BITSTOREAL '(' expr ')'              { $$ = new AstBitsToRealD{$1, $3}; }
        |       yD_BITSTOSHORTREAL '(' expr ')'         { $$ = new AstBitsToRealD{$1, $3}; UNSUPREAL($1); }
        |       yD_CEIL '(' expr ')'                    { $$ = new AstCeilD{$1, $3}; }
        |       yD_CHANGED '(' expr ')'                 { $$ = new AstLogNot{$1, new AstStable{$1, $3, nullptr}}; }
        |       yD_CHANGED '(' expr ',' expr ')'
                        { $$ = new AstLogNot{$1, new AstStable{$1, $3, GRAMMARP->createSenTreeChanged($1, $5)}}; }
        |       yD_CHANGED_GCLK '(' expr ')'
                        { $$ = new AstLogNot{$1, new AstStable{$1, $3, GRAMMARP->createGlobalClockSenTree($1)}}; }
        |       yD_CHANGING_GCLK '(' expr ')'
                        { $$ = new AstLogNot{$1, new AstSteady{$1, $3}}; }
        |       yD_CLOG2 '(' expr ')'                   { $$ = new AstCLog2{$1, $3}; }
        |       yD_COS '(' expr ')'                     { $$ = new AstCosD{$1, $3}; }
        |       yD_COSH '(' expr ')'                    { $$ = new AstCoshD{$1, $3}; }
        |       yD_COUNTBITS '(' expr ',' expr ')'              { $$ = new AstCountBits{$1, $3, $5}; }
        |       yD_COUNTBITS '(' expr ',' expr ',' expr ')'             { $$ = new AstCountBits{$1, $3, $5, $7}; }
        |       yD_COUNTBITS '(' expr ',' expr ',' expr ',' expr ')'    { $$ = new AstCountBits{$1, $3, $5, $7, $9}; }
        |       yD_COUNTBITS '(' expr ',' expr ',' expr ',' expr ',' exprList ')'
                        { $$ = new AstCountBits{$1, $3, $5, $7, $9};
                          BBUNSUP($11, "Unsupported: $countbits with more than 3 control fields"); }
        |       yD_COUNTONES '(' expr ')'               { $$ = new AstCountOnes{$1, $3}; }
        |       yD_DIMENSIONS '(' exprOrDataType ')'    { $$ = new AstAttrOf{$1, VAttrType::DIM_DIMENSIONS, $3}; }
        |       yD_DIST_CHI_SQUARE '(' expr ',' expr ')'        { $$ = new AstDistChiSquare{$1, $3, $5}; }
        |       yD_DIST_ERLANG '(' expr ',' expr ',' expr ')'   { $$ = new AstDistErlang{$1, $3, $5, $7}; }
        |       yD_DIST_EXPONENTIAL '(' expr ',' expr ')'       { $$ = new AstDistExponential{$1, $3, $5}; }
        |       yD_DIST_NORMAL '(' expr ',' expr ',' expr ')'   { $$ = new AstDistNormal{$1, $3, $5, $7}; }
        |       yD_DIST_POISSON '(' expr ',' expr ')'   { $$ = new AstDistPoisson{$1, $3, $5}; }
        |       yD_DIST_T '(' expr ',' expr ')'         { $$ = new AstDistT{$1, $3, $5}; }
        |       yD_DIST_UNIFORM '(' expr ',' expr ',' expr ')'  { $$ = new AstDistUniform{$1, $3, $5, $7}; }
        |       yD_EXP '(' expr ')'                     { $$ = new AstExpD{$1, $3}; }
        |       yD_FALLING_GCLK '(' expr ')'            { $$ = new AstFalling{$1, $3}; }
        |       yD_FELL '(' expr ')'                    { $$ = new AstFell{$1, $3, nullptr}; }
        |       yD_FELL '(' expr ',' expr ')'           { $$ = new AstFell{$1, $3, GRAMMARP->createSenTreeChanged($1, $5)}; }
        |       yD_FELL_GCLK '(' expr ')'               { $$ = new AstFell{$1, $3, GRAMMARP->createGlobalClockSenTree($1)}; }
        |       yD_FEOF '(' expr ')'                    { $$ = new AstFEof{$1, $3}; }
        |       yD_FERROR '(' expr ',' idClassSel ')'   { $$ = new AstFError{$1, $3, $5}; }
        |       yD_FGETC '(' expr ')'                   { $$ = new AstFGetC{$1, $3}; }
        |       yD_FGETS '(' expr ',' expr ')'          { $$ = new AstFGetS{$1, $3, $5}; }
        |       yD_FOPEN '(' expr ')'                   { $$ = new AstFOpenMcd{$1, $3}; }
        |       yD_FOPEN '(' expr ',' expr ')'          { $$ = new AstFOpen{$1, $3, $5}; }
        |       yD_FREAD '(' expr ',' expr ')'          { $$ = new AstFRead{$1, $3, $5, nullptr, nullptr}; }
        |       yD_FREAD '(' expr ',' expr ',' expr ')'  { $$ = new AstFRead{$1, $3, $5, $7, nullptr}; }
        |       yD_FREAD '(' expr ',' expr ',' expr ',' expr ')'  { $$ = new AstFRead{$1, $3, $5, $7, $9}; }
        |       yD_FREAD '(' expr ',' expr ',' ',' expr ')'  { $$ = new AstFRead{$1, $3, $5, nullptr, $8}; }
        |       yD_FREWIND '(' expr ')'                 { $$ = new AstFRewind{$1, $3}; }
        |       yD_FUTURE_GCLK '(' expr ')'             { $$ = new AstFuture{$1, $3, nullptr}; }
        |       yD_FLOOR '(' expr ')'                   { $$ = new AstFloorD{$1, $3}; }
        |       yD_FSCANF '(' expr ',' str commaVRDListE ')'    { $$ = new AstFScanF{$1, *$5, $3, $6}; }
        |       yD_FSEEK '(' expr ',' expr ',' expr ')' { $$ = new AstFSeek{$1, $3, $5, $7}; }
        |       yD_FTELL '(' expr ')'                   { $$ = new AstFTell{$1, $3}; }
        |       yD_GLOBAL_CLOCK parenE                  { $$ = GRAMMARP->createGlobalClockParseRef($1); }
        |       yD_HIGH '(' exprOrDataType ')'          { $$ = new AstAttrOf{$1, VAttrType::DIM_HIGH, $3, nullptr}; }
        |       yD_HIGH '(' exprOrDataType ',' expr ')' { $$ = new AstAttrOf{$1, VAttrType::DIM_HIGH, $3, $5}; }
        |       yD_HYPOT '(' expr ',' expr ')'          { $$ = new AstHypotD{$1, $3, $5}; }
        |       yD_INCREMENT '(' exprOrDataType ')'     { $$ = new AstAttrOf{$1, VAttrType::DIM_INCREMENT, $3, nullptr}; }
        |       yD_INCREMENT '(' exprOrDataType ',' expr ')'    { $$ = new AstAttrOf{$1, VAttrType::DIM_INCREMENT, $3, $5}; }
        |       yD_INFERRED_DISABLE parenE              { $$ = new AstInferredDisable{$1}; }
        |       yD_ISUNBOUNDED '(' expr ')'             { $$ = new AstIsUnbounded{$1, $3}; }
        |       yD_ISUNKNOWN '(' expr ')'               { $$ = new AstIsUnknown{$1, $3}; }
        |       yD_ITOR '(' expr ')'                    { $$ = new AstIToRD{$1, $3}; }
        |       yD_LEFT '(' exprOrDataType ')'          { $$ = new AstAttrOf{$1, VAttrType::DIM_LEFT, $3, nullptr}; }
        |       yD_LEFT '(' exprOrDataType ',' expr ')' { $$ = new AstAttrOf{$1, VAttrType::DIM_LEFT, $3, $5}; }
        |       yD_LN '(' expr ')'                      { $$ = new AstLogD{$1, $3}; }
        |       yD_LOG10 '(' expr ')'                   { $$ = new AstLog10D{$1, $3}; }
        |       yD_LOW '(' exprOrDataType ')'           { $$ = new AstAttrOf{$1, VAttrType::DIM_LOW, $3, nullptr}; }
        |       yD_LOW '(' exprOrDataType ',' expr ')'  { $$ = new AstAttrOf{$1, VAttrType::DIM_LOW, $3, $5}; }
        |       yD_ONEHOT '(' expr ')'                  { $$ = new AstOneHot{$1, $3}; }
        |       yD_ONEHOT0 '(' expr ')'                 { $$ = new AstOneHot0{$1, $3}; }
        |       yD_PAST '(' expr ')'                    { $$ = new AstPast{$1, $3}; }
        |       yD_PAST '(' expr ',' exprE ')'          { $$ = new AstPast{$1, $3, $5}; }
        |       yD_PAST '(' expr ',' exprE ',' exprE ')'
                        { if ($7) BBUNSUP($1, "Unsupported: $past expr2 and/or clock arguments");
                          DEL($7);
                          $$ = new AstPast{$1, $3, $5}; }
        |       yD_PAST '(' expr ',' exprE ',' exprE ',' clocking_eventE ')'
                        { if ($7 || $9) BBUNSUP($1, "Unsupported: $past expr2 and/or clock arguments");
                          DEL($7, $9);
                          $$ = new AstPast{$1, $3, $5}; }
        |       yD_PAST_GCLK '(' expr ')'               { $$ = new AstPast{$1, $3, nullptr, GRAMMARP->createGlobalClockSenTree($1)}; }
        |       yD_POW '(' expr ',' expr ')'            { $$ = new AstPowD{$1, $3, $5}; }
        |       yD_RANDOM '(' expr ')'                  { $$ = new AstRand{$1, $3, false}; }
        |       yD_RANDOM parenE                        { $$ = new AstRand{$1, nullptr, false}; }
        |       yD_REALTIME parenE                      { $$ = new AstTimeD{$1, VTimescale{VTimescale::NONE}}; }
        |       yD_REALTOBITS '(' expr ')'              { $$ = new AstRealToBits{$1, $3}; }
        |       yD_REWIND '(' expr ')'                  { $$ = new AstFSeek{$1, $3, new AstConst{$1, 0}, new AstConst{$1, 0}}; }
        |       yD_RIGHT '(' exprOrDataType ')'         { $$ = new AstAttrOf{$1, VAttrType::DIM_RIGHT, $3, nullptr}; }
        |       yD_RIGHT '(' exprOrDataType ',' expr ')'        { $$ = new AstAttrOf{$1, VAttrType::DIM_RIGHT, $3, $5}; }
        |       yD_RISING_GCLK '(' expr ')'             { $$ = new AstRising{$1, $3}; }
        |       yD_ROSE '(' expr ')'                    { $$ = new AstRose{$1, $3, nullptr}; }
        |       yD_ROSE '(' expr ',' expr ')'           { $$ = new AstRose{$1, $3, GRAMMARP->createSenTreeChanged($1, $5)}; }
        |       yD_ROSE_GCLK '(' expr ')'               { $$ = new AstRose{$1, $3, GRAMMARP->createGlobalClockSenTree($1)}; }
        |       yD_RTOI '(' expr ')'                    { $$ = new AstRToIS{$1, $3}; }
        |       yD_SAMPLED '(' expr ')'                 { $$ = new AstSampled{$1, $3}; }
        |       yD_SFORMATF '(' exprDispList ')'        { $$ = new AstSFormatF{$1, AstSFormatF::NoFormat{}, $3, 'd', false}; }
        |       yD_SHORTREALTOBITS '(' expr ')'         { $$ = new AstRealToBits{$1, $3}; UNSUPREAL($1); }
        |       yD_SIGNED '(' expr ')'                  { $$ = new AstSigned{$1, $3}; }
        |       yD_SIN '(' expr ')'                     { $$ = new AstSinD{$1, $3}; }
        |       yD_SINH '(' expr ')'                    { $$ = new AstSinhD{$1, $3}; }
        |       yD_SIZE '(' exprOrDataType ')'          { $$ = new AstAttrOf{$1, VAttrType::DIM_SIZE, $3, nullptr}; }
        |       yD_SIZE '(' exprOrDataType ',' expr ')' { $$ = new AstAttrOf{$1, VAttrType::DIM_SIZE, $3, $5}; }
        |       yD_SQRT '(' expr ')'                    { $$ = new AstSqrtD{$1, $3}; }
        |       yD_SSCANF '(' expr ',' str commaVRDListE ')'    { $$ = new AstSScanF{$1, *$5, $3, $6}; }
        |       yD_STABLE '(' expr ')'                  { $$ = new AstStable{$1, $3, nullptr}; }
        |       yD_STABLE '(' expr ',' expr ')'         { $$ = new AstStable{$1, $3, GRAMMARP->createSenTreeChanged($1, $5)}; }
        |       yD_STABLE_GCLK '(' expr ')'             { $$ = new AstStable{$1, $3, GRAMMARP->createGlobalClockSenTree($1)}; }
        |       yD_STEADY_GCLK '(' expr ')'             { $$ = new AstSteady{$1, $3}; }
        |       yD_STIME parenE
                        { $$ = new AstSel{$1, new AstTime{$1, VTimescale{VTimescale::NONE}}, 0, 32}; }
        |       yD_TAN '(' expr ')'                     { $$ = new AstTanD{$1, $3}; }
        |       yD_TANH '(' expr ')'                    { $$ = new AstTanhD{$1, $3}; }
        |       yD_TESTPLUSARGS '(' expr ')'            { $$ = new AstTestPlusArgs{$1, $3}; }
        |       yD_TIME parenE                          { $$ = new AstTime{$1, VTimescale{VTimescale::NONE}}; }
        |       yD_TIMEPRECISION                        { $$ = new AstTimePrecision{$1}; }
        |       yD_TIMEPRECISION '(' ')'                { $$ = new AstTimePrecision{$1}; }
        |       yD_TIMEPRECISION '(' idClassSel ')'     { $$ = new AstTimePrecision{$1}; DEL($3); }
        |       yD_TIMEUNIT                             { $$ = new AstTimeUnit{$1}; }
        |       yD_TIMEUNIT '(' ')'                     { $$ = new AstTimeUnit{$1}; }
        |       yD_TIMEUNIT '(' idClassSel ')'          { $$ = new AstTimeUnit{$1}; DEL($3); }
        |       yD_TYPENAME '(' exprOrDataType ')'      { $$ = new AstAttrOf{$1, VAttrType::TYPENAME, $3}; }
        |       yD_UNGETC '(' expr ',' expr ')'         { $$ = new AstFUngetC{$1, $5, $3}; }  // Arg swap to file first
        |       yD_UNPACKED_DIMENSIONS '(' exprOrDataType ')'   { $$ = new AstAttrOf{$1, VAttrType::DIM_UNPK_DIMENSIONS, $3}; }
        |       yD_UNSIGNED '(' expr ')'                { $$ = new AstUnsigned{$1, $3}; }
        |       yD_URANDOM '(' expr ')'                 { $$ = new AstRand{$1, $3, true}; }
        |       yD_URANDOM parenE                       { $$ = new AstRand{$1, nullptr, true}; }
        |       yD_URANDOM_RANGE '(' expr ')'           { $$ = new AstURandomRange{$1, $3, new AstConst{$1, 0}}; }
        |       yD_URANDOM_RANGE '(' expr ',' expr ')'  { $$ = new AstURandomRange{$1, $3, $5}; }
        |       yD_VALUEPLUSARGS '(' expr ',' expr ')'  { $$ = new AstValuePlusArgs{$1, $3, $5}; }
        ;

severity_system_task: // IEEE: severity_system_task/elaboration_severity_system_task (1800-2009)
        //                      // TODO: These currently just make initial statements, should instead give runtime error
                severity_system_task_guts ';'           { $$ = new AstInitial{$<fl>1, $1}; }
        ;

severity_system_task_guts:    // IEEE: part of severity_system_task (1800-2009)
        //                      // $fatal first argument is exit number, must be constant
                yD_INFO parenE                          { $$ = new AstElabDisplay{$1, VDisplayType::DT_INFO, nullptr}; }
        |       yD_INFO '(' exprList ')'                { $$ = new AstElabDisplay{$1, VDisplayType::DT_INFO, $3}; }
        |       yD_WARNING parenE                       { $$ = new AstElabDisplay{$1, VDisplayType::DT_WARNING, nullptr}; }
        |       yD_WARNING '(' exprList ')'             { $$ = new AstElabDisplay{$1, VDisplayType::DT_WARNING, $3}; }
        |       yD_ERROR parenE                         { $$ = new AstElabDisplay{$1, VDisplayType::DT_ERROR, nullptr}; }
        |       yD_ERROR '(' exprList ')'               { $$ = new AstElabDisplay{$1, VDisplayType::DT_ERROR, $3}; }
        |       yD_FATAL parenE                         { $$ = new AstElabDisplay{$1, VDisplayType::DT_FATAL, nullptr}; }
        |       yD_FATAL '(' expr ')'                   { $$ = new AstElabDisplay{$1, VDisplayType::DT_FATAL, nullptr}; DEL($3); }
        |       yD_FATAL '(' expr ',' exprListE ')'     { $$ = new AstElabDisplay{$1, VDisplayType::DT_FATAL, $5}; DEL($3); }
        ;

systemDpiArgsE:           // IEEE: part of system_if_call for arguments of $dpi call
                parenE                                  { $$ = nullptr; }
        |       '(' exprList ')'                        { $$ = GRAMMARP->argWrapList($2); }
        ;

property_actual_arg:  // ==IEEE: property_actual_arg
        //                      // IEEE: property_expr
        //                      // IEEE: sequence_actual_arg
        //UNSUP pev_expr                                { $$ = $1; }
        //UNSUP remove below:
                pexpr                                   { $$ = $1; }
        //                      // IEEE: sequence_expr
        //                      // property_expr already includes sequence_expr
        ;

exprOrDataType:          // expr | data_type: combined to prevent conflicts
                expr                                    { $$ = $1; }
        //                      // data_type includes id that overlaps expr, so special flavor
        //                      // data_type expanded:
        |       data_typeNoRef                          { $$ = $1; }
        //
        //                      // Conflicts with non-type id, resolved in V3LinkDot
        //                      // NO: packageClassScopeE idType packed_dimensionListE
        //
        |       packageClassScopeE idType parameter_value_assignmentClass packed_dimensionListE
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, $3};
                          $$ = GRAMMARP->createArray(refp, $4, true); }
        //                      // not in spec, but needed for $past(sig,1,,@(posedge clk))
        //UNSUP event_control                           { }
        ;

//UNSUPexprOrDataTypeOrMinTypMax<nodep>:  // exprOrDataType or mintypmax_expression
//UNSUP         expr                                    { $$ = $1; }
//UNSUP |       expr ':' expr ':' expr                  { $$ = $3; }
//UNSUP //                      // data_type includes id that overlaps expr, so special flavor
//UNSUP |       data_type                               { $$ = $1; }
//UNSUP //                      // not in spec, but needed for $past(sig,1,,@(posedge clk))
//UNSUP |       event_control                           { $$ = $1; }
//UNSUP ;

//UNSUPexprOrDataTypeList<nodep>:
//UNSUP         exprOrDataType                          { $$ = $1; }
//UNSUP |       exprOrDataTypeList ',' exprOrDataType   { $$ = addNextNull($1, $3); }
//UNSUP ;

list_of_argumentsE:  // IEEE: [list_of_arguments]
                argsDottedList                          { $$ = $1; }
        |       argsExprListE
                        { if (VN_IS($1, Arg) && VN_CAST($1, Arg)->emptyConnectNoNext()) {
                              $1->deleteTree(); $$ = nullptr;  // Mis-created when have 'func()'
                          } else { $$ = $1; } }
        |       argsExprListE ',' argsDottedList        { $$ = addNextNull($1, $3); }
        ;

task_declaration:   // ==IEEE: task_declaration
                yTASK dynamic_override_specifiersE lifetimeE taskId tfGuts yENDTASK endLabelE
                        { $$ = $4; $$->addStmtsp($5);
                          $$->baseOverride($2);
                          $$->lifetime($3);
                          GRAMMARP->endLabel($<fl>7, $$, $7); }
        ;

task_prototype:             // ==IEEE: task_prototype
                yTASK dynamic_override_specifiersE taskId '(' tf_port_listE ')'
                        { $$ = $3; $$->addStmtsp($5); $$->prototype(true); }
        |       yTASK dynamic_override_specifiersE taskId
                        { $$ = $3; $$->prototype(true); }
        ;

function_declaration:       // IEEE: function_declaration + function_body_declaration
                yFUNCTION dynamic_override_specifiersE lifetimeE funcId funcIsolateE tfGuts yENDFUNCTION endLabelE
                        { $$ = $4; $4->attrIsolateAssign($5); $$->addStmtsp($6);
                          $$->baseOverride($2);
                          $$->lifetime($3);
                          GRAMMARP->endLabel($<fl>8, $$, $8); }
        |       yFUNCTION dynamic_override_specifiersE lifetimeE funcIdNew funcIsolateE tfNewGuts yENDFUNCTION endLabelE
                        { $$ = $4; $4->attrIsolateAssign($5); $$->addStmtsp($6);
                          $$->baseOverride($2);
                          $$->lifetime($3);
                          GRAMMARP->endLabel($<fl>8, $$, $8); }
        ;

function_prototype: // IEEE: function_prototype
                yFUNCTION dynamic_override_specifiersE funcId '(' tf_port_listE ')'
                        { $$ = $3; $$->addStmtsp($5); $$->prototype(true); }
        |       yFUNCTION dynamic_override_specifiersE funcId
                        { $$ = $3; $$->prototype(true); }
        ;

class_constructor_prototype:        // ==IEEE: class_constructor_prototype
        //                      // IEEE has no dynamic_override_specifiersE,
        //                      // but required to avoid conflicts, so we must check after parsing
                yFUNCTION dynamic_override_specifiersE funcIdNew '(' class_constructor_arg_listE ')' ';'
                        { $$ = $3; $$->addStmtsp($5); $$->prototype(true); }
        |       yFUNCTION dynamic_override_specifiersE funcIdNew ';'
                        { $$ = $3; $$->prototype(true); }
        ;

funcIsolateE:
                /* empty */                             { $$ = 0; }
        |       yVL_ISOLATE_ASSIGNMENTS                 { $$ = 1; }
        ;

method_prototype:
                task_prototype                          { $$ = $1; }
        |       function_prototype                      { $$ = $1; }
        ;

lifetimeE:            // IEEE: [lifetime]
                /* empty */                             { $$ = VLifetime::NONE; }
        |       lifetime                                { $$ = $1; }
        ;

lifetime:             // ==IEEE: lifetime
        //                      // Note lifetime used by members is instead under memberQual
                ySTATIC__ETC                            { $$ = VLifetime::STATIC_EXPLICIT; }
        |       yAUTOMATIC                              { $$ = VLifetime::AUTOMATIC_EXPLICIT; }
        ;

taskId:
                id
                        { $$ = new AstTask{$<fl>$, *$1, nullptr};
                          $$->verilogTask(true); }
        //
        |       id/*interface_identifier*/ '.' idAny
                        { $$ = new AstTask{$<fl>$, *$3, nullptr};
                          $$->verilogTask(true);
                          BBUNSUP($2, "Unsupported: Out of block function declaration"); }
        //
        |       packageClassScope id
                        { $$ = new AstTask{$<fl>$, *$2, nullptr};
                          $$->verilogTask(true);
                          $$->classOrPackagep($1);
                          $$->classMethod(true); }
        ;

funcId:             // IEEE: function_data_type_or_implicit + part of function_body_declaration
        //                      // IEEE: function_data_type_or_implicit must be expanded here to prevent conflict
        //                      // function_data_type expanded here to prevent conflicts with
        //                      // implicit_type:empty vs data_type:ID
                /**/ fIdScoped
                        { $$ = $1;
                          $$->fvarp(new AstBasicDType{$<fl>1, LOGIC_IMPLICIT}); }
        |       signingE rangeList fIdScoped
                        { $$ = $3;
                          $$->fvarp(GRAMMARP->addRange(new AstBasicDType{$<fl>3, LOGIC_IMPLICIT, $1}, $2, true)); }
        |       signing fIdScoped
                        { $$ = $2;
                          $$->fvarp(new AstBasicDType{$<fl>2, LOGIC_IMPLICIT, $1}); }
        |       data_typeNoRef fIdScoped
                        { $$ = $2;
                          $$->fvarp($1); }
        |       packageClassScopeE idInstType packed_dimensionListE fIdScoped
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, nullptr};
                          $$ = $4;
                          $$->fvarp(GRAMMARP->createArray(refp, $3, true)); }
        |       packageClassScopeE idInstType parameter_value_assignmentClass packed_dimensionListE fIdScoped
                        { AstRefDType* const refp = new AstRefDType{$<fl>2, *$2, $1, $3};
                          $$ = $5;
                          $$->fvarp(GRAMMARP->createArray(refp, $4, true)); }
        //                      // To verilator tasks are the same as void functions (we separately detect time passing)
        |       yVOID taskId
                        { $$ = $2;  // Internals represent it as a task, not a function (TODO cleanup)
                          $$->verilogTask(false);
                          $$->verilogFunction(true); }
        ;

funcIdNew:          // IEEE: from class_constructor_declaration
                yNEW__ETC
                        { $$ = new AstFunc{$<fl>1, "new", nullptr, nullptr};
                          $$->verilogFunction(true);
                          $$->isConstructor(true); }
        |       yNEW__PAREN
                        { $$ = new AstFunc{$<fl>1, "new", nullptr, nullptr};
                          $$->verilogFunction(true);
                          $$->isConstructor(true); }
        |       packageClassScopeNoId yNEW__PAREN
                        { $$ = new AstFunc{$<fl>2, "new", nullptr, nullptr};
                          $$->verilogFunction(true);
                          $$->classOrPackagep($1);
                          $$->isConstructor(true);
                          $$->classMethod(true); }
        ;

fIdScoped:               // IEEE: part of function_body_declaration/task_body_declaration
        //                      // IEEE: [ interface_identifier '.' | class_scope ] function_identifier
                id
                        { $<fl>$ = $<fl>1;
                          $$ = new AstFunc{$<fl>$, *$1, nullptr, nullptr};
                          $$->verilogFunction(true); }
        //
        |       id/*interface_identifier*/ '.' idAny
                        { $<fl>$ = $<fl>1;
                          $$ = new AstFunc{$<fl>$, *$1, nullptr, nullptr};
                          $$->verilogFunction(true);
                          BBUNSUP($2, "Unsupported: Out of block function declaration"); }
        //
        |       packageClassScope id
                        { $<fl>$ = $<fl>1;
                          $$ = new AstFunc{$<fl>$, *$2, nullptr, nullptr};
                          $$->verilogFunction(true);
                          $$->classMethod(true);
                          $$->classOrPackagep($1); }
        ;

tfGuts:
                '(' tf_port_listE ')' ';' tfBodyE       { $$ = addNextNull($2, $5); }
        |       ';' tfBodyE                             { $$ = $2; }
        ;

tfNewGuts:
                '(' class_constructor_arg_listE ')' ';' tfBodyE       { $$ = addNextNull($2, $5); }
        |       ';' tfBodyE                             { $$ = $2; }
        ;

tfBodyE:                 // IEEE: part of function_body_declaration/task_body_declaration
                /* empty */                             { $$ = nullptr; }
        |       tf_item_declarationList                 { $$ = $1; }
        |       tf_item_declarationList stmtList        { $$ = addNextNull($1, $2); }
        |       stmtList                                { $$ = $1; }
        ;

tf_item_declarationList:
                tf_item_declaration                     { $$ = $1; }
        |       tf_item_declarationList tf_item_declaration     { $$ = addNextNull($1, $2); }
        ;

tf_item_declaration:     // ==IEEE: tf_item_declaration
                block_item_declaration                  { $$ = $1; }
        |       tf_port_declaration                     { $$ = $1; }
        |       tf_item_declarationVerilator            { $$ = $1; }
        ;

tf_item_declarationVerilator:    // Verilator extensions
                yVL_PUBLIC                              { $$ = new AstPragma{$1, VPragmaType::PUBLIC_TASK}; v3Global.dpi(true); }
        |       yVL_NO_INLINE_TASK                      { $$ = new AstPragma{$1, VPragmaType::NO_INLINE_TASK}; }
        ;

tf_port_listE:           // IEEE: tf_port_list + empty
        //                      // Empty covered by tf_port_item
                /*empty*/
        /*mid*/         { VARRESET_LIST(UNKNOWN); VARIO(INPUT); }
        /*cont*/    tf_port_listList                    { $$ = $2; VARRESET_NONLIST(UNKNOWN); }
        ;

tf_port_listList:        // IEEE: part of tf_port_list
                tf_port_item                            { $$ = $1; }
        |       tf_port_listList ',' tf_port_item       { $$ = addNextNull($1, $3); }
        ;

class_constructor_arg_listE:  // IEEE: class_constructor_arg_list or empty
                /*empty*/
        /*mid*/         { VARRESET_LIST(UNKNOWN); VARIO(INPUT); }
        /*cont*/    class_constructor_arg_listList      { $$ = $2; VARRESET_NONLIST(UNKNOWN); }
        ;

class_constructor_arg_listList:  // IEEE: part of class_constructor_arg_list
                class_constructor_arg                   { $$ = $1; }
        |       class_constructor_arg_listList ',' class_constructor_arg       { $$ = addNextNull($1, $3); }
        ;

class_constructor_arg:  // ==IEEE: class_constructor_arg
                tf_port_item                            { $$ = $1; }
        |       yDEFAULT                                { $$ = nullptr; BBUNSUP($1, "Unsupported: new constructor 'default' argument"); }
        ;

tf_port_item:            // ==IEEE: tf_port_item
        //                      // We split tf_port_item into the type and assignment as don't know what follows a comma
                /* empty */                             { $$ = nullptr; PINNUMINC(); }  // For example a ",," port
        |       tf_port_itemFront tf_port_itemAssignment { $$ = $2; }
        |       tf_port_itemAssignment                  { $$ = $1; }
        ;

tf_port_itemFront:              // IEEE: part of tf_port_item, which has the data type
                data_type                               { VARDTYPE($1); }
        |       signingE rangeList
                        { AstNodeDType* const dtp = GRAMMARP->addRange(
                              new AstBasicDType{$2->fileline(), LOGIC_IMPLICIT, $1}, $2, true);
                          VARDTYPE(dtp); }
        |       signing
                        { AstNodeDType* const dtp = new AstBasicDType{$<fl>1, LOGIC_IMPLICIT, $1};
                          VARDTYPE(dtp); }
        |       yVAR data_type                          { VARDTYPE($2); }
        |       yVAR implicit_typeE                     { VARDTYPE($2); }
        //
        |       tf_port_itemDir /*implicit*/            { VARDTYPE(nullptr); /*default_nettype-see spec*/ }
        |       tf_port_itemDir data_type               { VARDTYPE($2); }
        |       tf_port_itemDir signingE rangeList
                        { AstNodeDType* const dtp = GRAMMARP->addRange(
                              new AstBasicDType{$3->fileline(), LOGIC_IMPLICIT, $2}, $3, true);
                          VARDTYPE(dtp); }
        |       tf_port_itemDir signing
                        { AstNodeDType* const dtp = new AstBasicDType{$<fl>2, LOGIC_IMPLICIT, $2};
                          VARDTYPE(dtp); }
        |       tf_port_itemDir yVAR data_type          { VARDTYPE($3); }
        |       tf_port_itemDir yVAR implicit_typeE     { VARDTYPE($3); }
        ;

tf_port_itemDir:                // IEEE: part of tf_port_item, direction
                port_direction                          { }  // port_direction sets VARIO
        ;

tf_port_itemAssignment:   // IEEE: part of tf_port_item, which has assignment
                id variable_dimensionListE sigAttrListE exprEqE
                        { $$ = VARDONEA($<fl>1, *$1, $2, $3); if ($4) $$->valuep($4); }
        ;

parenE:
                /* empty */                             { }
        |       '(' ')'                                 { }
        ;

//      method_call:            // ==IEEE: method_call + method_call_body
//                              // IEEE: method_call_root '.' method_identifier [ '(' list_of_arguments ')' ]
//                              //   "method_call_root '.' method_identifier" looks just like "expr '.' id"
//                              //   "method_call_root '.' method_identifier (...)" looks just like "expr '.' tf_call"
//                              // IEEE: built_in_method_call
//                              //   method_call_root not needed, part of expr resolution
//                              // What's left is below array_methodNoRoot
array_methodNoRoot:
                yOR                                     { $$ = new AstFuncRef{$1, "or", nullptr}; }
        |       yAND                                    { $$ = new AstFuncRef{$1, "and", nullptr}; }
        |       yXOR                                    { $$ = new AstFuncRef{$1, "xor", nullptr}; }
        |       yUNIQUE                                 { $$ = new AstFuncRef{$1, "unique", nullptr}; }
        ;

array_methodWith:
                array_methodNoRoot parenE               { $$ = $1; }
        |       array_methodNoRoot parenE yWITH__PAREN '(' expr ')'
                        { $$ = new AstWithParse{$3, $1, $5}; }
        |       array_methodNoRoot '(' expr ')' yWITH__PAREN '(' expr ')'
                        { $$ = new AstWithParse{$5, $1, $7}; $1->addPinsp(new AstArg{$<fl>3, "", $3}); }
        ;

dpi_import_export:       // ==IEEE: dpi_import_export
                yIMPORT yaSTRING dpi_tf_import_propertyE dpi_importLabelE function_prototype ';'
                        { $$ = $5;
                          if (*$4 != "") $5->cname(*$4);
                          $5->dpiContext($3 == iprop_CONTEXT);
                          $5->dpiPure($3 == iprop_PURE);
                          $5->dpiImport(true);
                          GRAMMARP->checkDpiVer($1, *$2); v3Global.dpi(true); }
        |       yIMPORT yaSTRING dpi_tf_import_propertyE dpi_importLabelE task_prototype ';'
                        { $$ = $5;
                          if (*$4 != "") $5->cname(*$4);
                          $5->dpiContext($3 == iprop_CONTEXT);
                          $5->dpiPure($3 == iprop_PURE);
                          $5->dpiImport(true);
                          $5->dpiTask(true);
                          GRAMMARP->checkDpiVer($1, *$2); v3Global.dpi(true); }
        |       yEXPORT yaSTRING dpi_importLabelE yFUNCTION idAny ';'
                        { $$ = new AstDpiExport{$<fl>5, *$5, *$3};
                          GRAMMARP->checkDpiVer($1, *$2); v3Global.dpi(true); }
        |       yEXPORT yaSTRING dpi_importLabelE yTASK     idAny ';'
                        { $$ = new AstDpiExport{$<fl>5, *$5, *$3};
                          GRAMMARP->checkDpiVer($1, *$2); v3Global.dpi(true); }
        ;

dpi_importLabelE:         // IEEE: part of dpi_import_export
                /* empty */                             { static string s; $$ = &s; }
        |       idAny/*c_identifier*/ '='               { $$ = $1; $<fl>$ = $<fl>1; }
        ;

dpi_tf_import_propertyE: // IEEE: [ dpi_function_import_property + dpi_task_import_property ]
                /* empty */                             { $$ = iprop_NONE; }
        |       yCONTEXT                                { $$ = iprop_CONTEXT; }
        |       yPURE                                   { $$ = iprop_PURE; }
        ;


//************************************************
// Expressions
//
//  means this is the (l)eft hand side of any operator
//     it will get replaced by "", "f" or "s"equence
//  means this is a (r)ight hand later expansion in the same statement,
//     not under parenthesis for <= disambiguation
//     it will get replaced by "", or "f"
//  means this is a (p)arenthetized expression
//     it will get replaced by "", or "s"equence

exprEqE:             // IEEE: optional '=' expression (part of param_assignment)
        //                      // constant_param_expression: '$' is in expr
                /*empty*/                               { $$ = nullptr; }
        |       '=' expr                                { $$ = $2; }
        ;

exprOrDataTypeEqE:       // IEEE: optional '=' expression (part of param_assignment)
        //                      // constant_param_expression: '$' is in expr
                /*empty*/                               { $$ = nullptr; }
        |       '=' exprOrDataType                      { $$ = $2; }
        ;

constExpr:
                expr                                    { $$ = $1; }
        ;

exprE:               // IEEE: optional expression
                /*empty*/                               { $$ = nullptr; }
        |       expr                                    { $$ = $1; }
        ;

expr:                // IEEE: part of expression/constant_expression/primary
        // *SEE BELOW*          // IEEE: primary/constant_primary
        //
        //                      // IEEE: unary_operator primary
                '+' expr     %prec prUNARYARITH      { $$ = $2; }
        |       '-' expr     %prec prUNARYARITH      { $$ = new AstNegate{$1, $2}; }
        |       '!' expr     %prec prNEGATION        { $$ = new AstLogNot{$1, $2}; }
        |       '&' expr     %prec prREDUCTION       { $$ = new AstRedAnd{$1, $2}; }
        |       '~' expr     %prec prNEGATION        { $$ = new AstNot{$1, $2}; }
        |       '|' expr     %prec prREDUCTION       { $$ = new AstRedOr{$1, $2}; }
        |       '^' expr     %prec prREDUCTION       { $$ = new AstRedXor{$1, $2}; }
        |       yP_NAND expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedAnd{$1, $2}}; }
        |       yP_NOR  expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedOr{$1, $2}}; }
        |       yP_XNOR expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedXor{$1, $2}}; }
        //
        //                      // IEEE: inc_or_dec_expression
        |       inc_or_dec_expression                { $<fl>$ = $<fl>1; $$ = $1; }
        //
        //                      // IEEE: '(' operator_assignment ')'
        //                      // Need exprScope of variable_lvalue to prevent conflict
        |       '(' exprScope '='          expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, $4},
                                               $2->cloneTreePure(true)};
                          ASSIGNEQEXPR($<fl>3); }
        |       '(' exprScope yP_PLUSEQ    expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAdd{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' exprScope yP_MINUSEQ   expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstSub{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' exprScope yP_TIMESEQ   expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstMul{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' exprScope yP_DIVEQ     expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstDiv{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' exprScope yP_MODEQ     expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstModDiv{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' exprScope yP_ANDEQ     expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAnd{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' exprScope yP_OREQ      expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstOr{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' exprScope yP_XOREQ     expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstXor{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' exprScope yP_SLEFTEQ   expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftL{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' exprScope yP_SRIGHTEQ  expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftR{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        |       '(' exprScope yP_SSRIGHTEQ expr ')'
                        { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftRS{$3, $2->cloneTreePure(true), $4}},
                                               $2->cloneTreePure(true)}; }
        //
        //                      // IEEE: expression binary_operator expression
        |       expr '+' expr                     { $$ = new AstAdd{$2, $1, $3}; }
        |       expr '-' expr                     { $$ = new AstSub{$2, $1, $3}; }
        |       expr '*' expr                     { $$ = new AstMul{$2, $1, $3}; }
        |       expr '/' expr                     { $$ = new AstDiv{$2, $1, $3}; }
        |       expr '%' expr                     { $$ = new AstModDiv{$2, $1, $3}; }
        |       expr yP_EQUAL expr                { $$ = new AstEq{$2, $1, $3}; }
        |       expr yP_NOTEQUAL expr             { $$ = new AstNeq{$2, $1, $3}; }
        |       expr yP_CASEEQUAL expr            { $$ = new AstEqCase{$2, $1, $3}; }
        |       expr yP_CASENOTEQUAL expr         { $$ = new AstNeqCase{$2, $1, $3}; }
        |       expr yP_WILDEQUAL expr            { $$ = new AstEqWild{$2, $1, $3}; }
        |       expr yP_WILDNOTEQUAL expr         { $$ = new AstNeqWild{$2, $1, $3}; }
        |       expr yP_ANDAND expr               { $$ = new AstLogAnd{$2, $1, $3}; }
        |       expr yP_OROR expr                 { $$ = new AstLogOr{$2, $1, $3}; }
        |       expr yP_POW expr                  { $$ = new AstPow{$2, $1, $3}; }
        |       expr '<' expr                     { $$ = new AstLt{$2, $1, $3}; }
        |       expr '>' expr                     { $$ = new AstGt{$2, $1, $3}; }
        |       expr yP_GTE expr                  { $$ = new AstGte{$2, $1, $3}; }
        |       expr '&' expr                     { $$ = new AstAnd{$2, $1, $3}; }
        |       expr '|' expr                     { $$ = new AstOr{$2, $1, $3}; }
        |       expr '^' expr                     { $$ = new AstXor{$2, $1, $3}; }
        |       expr yP_XNOR expr                 { $$ = new AstNot{$2, new AstXor{$2, $1, $3}}; }
        |       expr yP_NOR expr                  { $$ = new AstNot{$2, new AstOr{$2, $1, $3}}; }
        |       expr yP_NAND expr                 { $$ = new AstNot{$2, new AstAnd{$2, $1, $3}}; }
        |       expr yP_SLEFT expr                { $$ = new AstShiftL{$2, $1, $3}; }
        |       expr yP_SRIGHT expr               { $$ = new AstShiftR{$2, $1, $3}; }
        |       expr yP_SSRIGHT expr              { $$ = new AstShiftRS{$2, $1, $3}; }
        |       expr yP_LTMINUSGT expr            { $$ = new AstLogEq{$2, $1, $3}; }
        //
        //                      // IEEE: expression binary_operator expression (type compare see IEEE footnote)
        |       type_referenceEq yP_CASEEQUAL type_referenceBoth     { $$ = new AstEqT{$2, $1, $3}; }
        |       type_referenceEq yP_CASENOTEQUAL type_referenceBoth  { $$ = new AstNeqT{$2, $1, $3}; }
        |       type_referenceEq yP_EQUAL type_referenceBoth         { $$ = new AstEqT{$2, $1, $3}; }
        |       type_referenceEq yP_NOTEQUAL type_referenceBoth      { $$ = new AstNeqT{$2, $1, $3}; }
        //                      // IEEE: expr yP_MINUSGT expr  (1800-2009)
        //                      // Conflicts with constraint_expression:"expr yP_MINUSGT constraint_set"
        //                      // To duplicating expr for constraints, just allow the more general form
        //                      // Later Ast processing must ignore constraint terms where inappropriate
        //UNSUP expr yP_MINUSGT constraint_set               { $<fl>$ = $<fl>1; $$ = $1 + $2 + $3; }
        //UNSUP remove line below
        |       expr yP_MINUSGT expr              { $$ = new AstLogIf{$2, $1, $3}; }
        //
        //                      // <= is special, as we need to disambiguate it with <= assignment
        //                      // We copy all of expr to fexpr and rename this token to a fake one.
        |       expr yP_LTE expr       { $$ = new AstLte{$2, $1, $3}; }
        //
        //                      // IEEE: conditional_expression
        |       expr '?' expr ':' expr         { $$ = new AstCond{$2, $1, $3, $5}; }
        //
        //                      // IEEE: inside_expression
        |       expr yINSIDE '{' range_list '}'      { $$ = new AstInside{$2, $1, $4}; }
        //
        //                      // IEEE: tagged_union_expression
        //UNSUP yTAGGED id/*member*/ %prec prTAGGED             { $$ = $2; BBUNSUP("tagged reference"); }
        //                      // Spec only allows primary
        //UNSUP yTAGGED id/*member*/ %prec prTAGGED expr /*primary*/     { $$ = $2; BBUNSUP("tagged reference"); }
        //
        //======================// IEEE: primary/constant_primary
        //
        //                      // IEEE: primary_literal (minus string, which is handled specially)
        |       yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }
        |       yaFLOATNUM                              { $$ = new AstConst{$<fl>1, AstConst::RealDouble{}, $1}; }
        |       timeNumAdjusted                         { $$ = $1; }
        |       strAsInt                 { $$ = $1; }
        //
        //                      // IEEE: "... hierarchical_identifier select"  see below
        //
        //                      // IEEE: empty_unpacked_array_concatenation
        //                      // IEEE: (aka empty_queue, empty_unpacked_array_concatenation)
        |       '{' '}'                                 { $$ = new AstEmptyQueue{$1}; }
        //
        //                      // IEEE: concatenation/constant_concatenation
        //                      // Part of exprOkLvalue below
        //
        //                      // IEEE: multiple_concatenation/constant_multiple_concatenation
        |       '{' constExpr '{' cateList '}' '}'
                        { $$ = new AstReplicate{$3, $4, $2}; }
        |       '{' constExpr '{' cateList '}' '}' '[' expr ']'
                        { $$ = new AstSelBit{$7, new AstReplicate{$3, $4, $2}, $8}; }
        |       '{' constExpr '{' cateList '}' '}' '[' constExpr ':' constExpr ']'
                        { $$ = new AstSelExtract{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }
        |       '{' constExpr '{' cateList '}' '}' '[' expr yP_PLUSCOLON constExpr ']'
                        { $$ = new AstSelPlus{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }
        |       '{' constExpr '{' cateList '}' '}' '[' expr yP_MINUSCOLON constExpr ']'
                        { $$ = new AstSelMinus{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }
        //                      // UNSUP some other rules above
        //
        //                      // IEEE grammar error: function_subroutine_call [ range_expression ]
        //                      // should be instead:  function_subroutine_call [ part_select_range ]
        |       function_subroutine_callNoMethod
                        { $$ = $1; }
        |       function_subroutine_callNoMethod part_select_rangeList
                        { $$ = GRAMMARP->scrubSel($1, $2); }
        //                      // method_call
        |       expr '.' function_subroutine_callNoMethod
                        { $$ = new AstDot{$2, false, $1, $3}; }
        |       expr '.' function_subroutine_callNoMethod part_select_rangeList
                        { $$ = GRAMMARP->scrubSel(new AstDot{$2, false, $1, $3}, $4); }
        //                      // method_call:array_method requires a '.'
        |       expr '.' array_methodWith
                        { $$ = new AstDot{$2, false, $1, $3}; }
        |       expr '.' array_methodWith part_select_rangeList
                        { $$ = GRAMMARP->scrubSel(new AstDot{$2, false, $1, $3}, $4); }
        //
        //                      // IEEE: let_expression
        //                      // see funcRef
        //
        //                      // IEEE: '(' mintypmax_expression ')'
        |       '(' expr ')'             { $$ = $2; }
        |       '(' expr ':' expr ':' expr ')'
                        { $$ = $4; MINTYPMAXDLYUNSUP($4); DEL($2); DEL($6); }
        //                      // PSL rule
        |       '_' '(' expr ')'                        { $$ = $3; }    // Arbitrary Verilog inside PSL
        //
        //                      // IEEE: cast/constant_cast
        //                      // expanded from casting_type
        |       simple_typeNoRef yP_TICK '(' expr ')'
                        { $$ = new AstCast{$2, $4, VFlagChildDType{}, $1}; }
        //                      // expanded from simple_type ps_type_identifier (part of simple_type)
        //                      // expanded from simple_type ps_parameter_identifier (part of simple_type)
        //                      // Causes conflict, so handled post-parse
        //                      // NO: packageClassScopeE idType yP_TICK '(' expr ')'
        //
        |       yTYPE__ETC '(' exprOrDataType ')' yP_TICK '(' expr ')'
                        { $$ = new AstCast{$1, $7, VFlagChildDType{},
                                           new AstRefDType{$1, AstRefDType::FlagTypeOfExpr{}, $3}}; }
        |       ySIGNED yP_TICK '(' expr ')'            { $$ = new AstSigned{$1, $4}; }
        |       yUNSIGNED yP_TICK '(' expr ')'          { $$ = new AstUnsigned{$1, $4}; }
        |       ySTRING yP_TICK '(' expr ')'            { $$ = new AstCvtPackString{$1, $4}; }
        |       yCONST__ETC yP_TICK '(' expr ')'        { $$ = $4; }  // Not linting const presently
        //                      // Spec only allows primary with addition of a type reference
        //                      // We'll be more general, and later assert LHS was a type.
        |       expr yP_TICK '(' expr ')'            { $$ = new AstCastParse{$2, $4, $1}; }
        //
        //                      // IEEE: assignment_pattern_expression
        //                      // IEEE: streaming_concatenation
        //                      // See exprOkLvalue
        //
        //                      // IEEE: sequence_method_call
        //                      // Indistinguishable from function_subroutine_call:method_call
        //
        |       '$'                                     { $$ = new AstUnbounded{$<fl>1}; }
        |       yNULL                                   { $$ = new AstConst{$1, AstConst::Null{}}; }
        //                      // IEEE: yTHIS
        //                      // See exprScope
        //
        //----------------------
        //
        //                      // Part of expr that may also be used as lvalue
        |       exprOkLvalue                         { $$ = $1; }
        //
        //----------------------
        //
        //                      // IEEE: cond_predicate - here to avoid reduce problems
        //                      // Note expr includes cond_pattern
        |       expr yP_ANDANDAND expr            { $$ = new AstConst{$2, AstConst::BitFalse{}};
                                                          BBUNSUP($<fl>2, "Unsupported: &&& expression"); }
        //
        //                      // IEEE: cond_pattern - here to avoid reduce problems
        //                      // "expr yMATCHES pattern"
        //                      // IEEE: pattern - expanded here to avoid conflicts
        |       expr yMATCHES patternNoExpr          { $$ = new AstConst{$2, AstConst::BitFalse{}};
                                                          BBUNSUP($<fl>2, "Unsupported: matches operator"); }
        |       expr yMATCHES expr                { $$ = new AstConst{$2, AstConst::BitFalse{}};
                                                          BBUNSUP($<fl>2, "Unsupported: matches operator"); }
        //
        //                      // IEEE: expression_or_dist - here to avoid reduce problems
        //                      // "expr yDIST '{' dist_list '}'"
        |       expr yDIST '{' dist_list '}'         { $$ = new AstDist{$2, $1, $4}; }
        ;

fexpr:                   // For use as first part of statement (disambiguates <=)
                                 '+' fexpr     %prec prUNARYARITH      { $$ = $2; }         |       '-' fexpr     %prec prUNARYARITH      { $$ = new AstNegate{$1, $2}; }         |       '!' fexpr     %prec prNEGATION        { $$ = new AstLogNot{$1, $2}; }         |       '&' fexpr     %prec prREDUCTION       { $$ = new AstRedAnd{$1, $2}; }         |       '~' fexpr     %prec prNEGATION        { $$ = new AstNot{$1, $2}; }         |       '|' fexpr     %prec prREDUCTION       { $$ = new AstRedOr{$1, $2}; }         |       '^' fexpr     %prec prREDUCTION       { $$ = new AstRedXor{$1, $2}; }         |       yP_NAND fexpr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedAnd{$1, $2}}; }         |       yP_NOR  fexpr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedOr{$1, $2}}; }         |       yP_XNOR fexpr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedXor{$1, $2}}; }         |       finc_or_dec_expression                { $<fl>$ = $<fl>1; $$ = $1; }         |       '(' exprScope '='          expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, $4},                                                $2->cloneTreePure(true)};                           ASSIGNEQEXPR($<fl>3); }         |       '(' exprScope yP_PLUSEQ    expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAdd{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_MINUSEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstSub{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_TIMESEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstMul{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_DIVEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstDiv{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_MODEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstModDiv{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_ANDEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAnd{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_OREQ      expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstOr{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_XOREQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstXor{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_SLEFTEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftL{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_SRIGHTEQ  expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftR{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_SSRIGHTEQ expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftRS{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       fexpr '+' fexpr                     { $$ = new AstAdd{$2, $1, $3}; }         |       fexpr '-' fexpr                     { $$ = new AstSub{$2, $1, $3}; }         |       fexpr '*' fexpr                     { $$ = new AstMul{$2, $1, $3}; }         |       fexpr '/' fexpr                     { $$ = new AstDiv{$2, $1, $3}; }         |       fexpr '%' fexpr                     { $$ = new AstModDiv{$2, $1, $3}; }         |       fexpr yP_EQUAL fexpr                { $$ = new AstEq{$2, $1, $3}; }         |       fexpr yP_NOTEQUAL fexpr             { $$ = new AstNeq{$2, $1, $3}; }         |       fexpr yP_CASEEQUAL fexpr            { $$ = new AstEqCase{$2, $1, $3}; }         |       fexpr yP_CASENOTEQUAL fexpr         { $$ = new AstNeqCase{$2, $1, $3}; }         |       fexpr yP_WILDEQUAL fexpr            { $$ = new AstEqWild{$2, $1, $3}; }         |       fexpr yP_WILDNOTEQUAL fexpr         { $$ = new AstNeqWild{$2, $1, $3}; }         |       fexpr yP_ANDAND fexpr               { $$ = new AstLogAnd{$2, $1, $3}; }         |       fexpr yP_OROR fexpr                 { $$ = new AstLogOr{$2, $1, $3}; }         |       fexpr yP_POW fexpr                  { $$ = new AstPow{$2, $1, $3}; }         |       fexpr '<' fexpr                     { $$ = new AstLt{$2, $1, $3}; }         |       fexpr '>' fexpr                     { $$ = new AstGt{$2, $1, $3}; }         |       fexpr yP_GTE fexpr                  { $$ = new AstGte{$2, $1, $3}; }         |       fexpr '&' fexpr                     { $$ = new AstAnd{$2, $1, $3}; }         |       fexpr '|' fexpr                     { $$ = new AstOr{$2, $1, $3}; }         |       fexpr '^' fexpr                     { $$ = new AstXor{$2, $1, $3}; }         |       fexpr yP_XNOR fexpr                 { $$ = new AstNot{$2, new AstXor{$2, $1, $3}}; }         |       fexpr yP_NOR fexpr                  { $$ = new AstNot{$2, new AstOr{$2, $1, $3}}; }         |       fexpr yP_NAND fexpr                 { $$ = new AstNot{$2, new AstAnd{$2, $1, $3}}; }         |       fexpr yP_SLEFT fexpr                { $$ = new AstShiftL{$2, $1, $3}; }         |       fexpr yP_SRIGHT fexpr               { $$ = new AstShiftR{$2, $1, $3}; }         |       fexpr yP_SSRIGHT fexpr              { $$ = new AstShiftRS{$2, $1, $3}; }         |       fexpr yP_LTMINUSGT fexpr            { $$ = new AstLogEq{$2, $1, $3}; }         |       type_referenceEq yP_CASEEQUAL type_referenceBoth     { $$ = new AstEqT{$2, $1, $3}; }         |       type_referenceEq yP_CASENOTEQUAL type_referenceBoth  { $$ = new AstNeqT{$2, $1, $3}; }         |       type_referenceEq yP_EQUAL type_referenceBoth         { $$ = new AstEqT{$2, $1, $3}; }         |       type_referenceEq yP_NOTEQUAL type_referenceBoth      { $$ = new AstNeqT{$2, $1, $3}; }         |       fexpr yP_MINUSGT fexpr              { $$ = new AstLogIf{$2, $1, $3}; }         |       fexpr yP_LTE__IGNORE fexpr       { $$ = new AstLte{$2, $1, $3}; }         |       fexpr '?' fexpr ':' fexpr         { $$ = new AstCond{$2, $1, $3, $5}; }         |       fexpr yINSIDE '{' range_list '}'      { $$ = new AstInside{$2, $1, $4}; }         |       yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }         |       yaFLOATNUM                              { $$ = new AstConst{$<fl>1, AstConst::RealDouble{}, $1}; }         |       timeNumAdjusted                         { $$ = $1; }         |       strAsInt                 { $$ = $1; }         |       '{' '}'                                 { $$ = new AstEmptyQueue{$1}; }         |       '{' constExpr '{' cateList '}' '}'                         { $$ = new AstReplicate{$3, $4, $2}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr ']'                         { $$ = new AstSelBit{$7, new AstReplicate{$3, $4, $2}, $8}; }         |       '{' constExpr '{' cateList '}' '}' '[' constExpr ':' constExpr ']'                         { $$ = new AstSelExtract{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr yP_PLUSCOLON constExpr ']'                         { $$ = new AstSelPlus{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr yP_MINUSCOLON constExpr ']'                         { $$ = new AstSelMinus{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       function_subroutine_callNoMethod                         { $$ = $1; }         |       function_subroutine_callNoMethod part_select_rangeList                         { $$ = GRAMMARP->scrubSel($1, $2); }         |       fexpr '.' function_subroutine_callNoMethod                         { $$ = new AstDot{$2, false, $1, $3}; }         |       fexpr '.' function_subroutine_callNoMethod part_select_rangeList                         { $$ = GRAMMARP->scrubSel(new AstDot{$2, false, $1, $3}, $4); }         |       fexpr '.' array_methodWith                         { $$ = new AstDot{$2, false, $1, $3}; }         |       fexpr '.' array_methodWith part_select_rangeList                         { $$ = GRAMMARP->scrubSel(new AstDot{$2, false, $1, $3}, $4); }         |       '(' expr ')'             { $$ = $2; }         |       '(' expr ':' expr ':' expr ')'                         { $$ = $4; MINTYPMAXDLYUNSUP($4); DEL($2); DEL($6); }         |       '_' '(' expr ')'                        { $$ = $3; }         |       simple_typeNoRef yP_TICK '(' expr ')'                         { $$ = new AstCast{$2, $4, VFlagChildDType{}, $1}; }         |       yTYPE__ETC '(' exprOrDataType ')' yP_TICK '(' expr ')'                         { $$ = new AstCast{$1, $7, VFlagChildDType{},                                            new AstRefDType{$1, AstRefDType::FlagTypeOfExpr{}, $3}}; }         |       ySIGNED yP_TICK '(' expr ')'            { $$ = new AstSigned{$1, $4}; }         |       yUNSIGNED yP_TICK '(' expr ')'          { $$ = new AstUnsigned{$1, $4}; }         |       ySTRING yP_TICK '(' expr ')'            { $$ = new AstCvtPackString{$1, $4}; }         |       yCONST__ETC yP_TICK '(' expr ')'        { $$ = $4; }         |       fexpr yP_TICK '(' expr ')'            { $$ = new AstCastParse{$2, $4, $1}; }         |       '$'                                     { $$ = new AstUnbounded{$<fl>1}; }         |       yNULL                                   { $$ = new AstConst{$1, AstConst::Null{}}; }         |       fexprOkLvalue                         { $$ = $1; }         |       fexpr yP_ANDANDAND fexpr            { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: &&& expression"); }         |       fexpr yMATCHES patternNoExpr          { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: matches operator"); }         |       fexpr yMATCHES fexpr                { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: matches operator"); }         |       fexpr yDIST '{' dist_list '}'         { $$ = new AstDist{$2, $1, $4}; }    // {copied}
        ;

//UNSUPpev_expr<nodeExprp>:  // IEEE: event_expression
//UNSUP //                      // for yOR/, see event_expression
//UNSUP //
//UNSUP //                      // IEEE: [ edge_identifier ] expression [ yIFF expression ]
//UNSUP //                      // expr alone see below
//UNSUP         senitemEdge                             { $$ = $1; }
//UNSUP |       ev_expr yIFF expr                       { }
//UNSUP //
//UNSUP //                      // IEEE: sequence_instance [ yIFF expression ]
//UNSUP //                      // seq_inst is in expr, so matches senitem rule above
//UNSUP //
//UNSUP //                      // IEEE: event_expression yOR event_expression
//UNSUP |       ev_expr yOR ev_expr                     { }
//UNSUP //                      // IEEE: event_expression ',' event_expression
//UNSUP //                      // See real event_expression rule
//UNSUP //
//UNSUP //---------------------
//UNSUP //                      // IEEE: expr
//UNSUP |       BISONPRE_COPY(expr,{s//ev_/g; s//ev_/g; s//ev_/g; s/'.'/yP_PAR__IGNORE /g;})  // {copied}
//UNSUP //
//UNSUP //                      // IEEE: '(' event_expression ')'
//UNSUP //                      // expr:'(' x ')' conflicts with event_expression:'(' event_expression ')'
//UNSUP //                      // so we use a special expression class
//UNSUP |       '(' event_expression ')'                { $<fl>$ = $<fl>1; $$ = "(...)"; }
//UNSUP //                      // IEEE: From normal expr: '(' expr ':' expr ':' expr ')'
//UNSUP //                      // But must avoid conflict
//UNSUP |       '(' event_expression ':' expr ':' expr ')'      { $<fl>$ = $<fl>1; $$ = "(...)"; }
//UNSUP ;

exprNoStr:               // expression with string removed
                                 '+' expr     %prec prUNARYARITH      { $$ = $2; }         |       '-' expr     %prec prUNARYARITH      { $$ = new AstNegate{$1, $2}; }         |       '!' expr     %prec prNEGATION        { $$ = new AstLogNot{$1, $2}; }         |       '&' expr     %prec prREDUCTION       { $$ = new AstRedAnd{$1, $2}; }         |       '~' expr     %prec prNEGATION        { $$ = new AstNot{$1, $2}; }         |       '|' expr     %prec prREDUCTION       { $$ = new AstRedOr{$1, $2}; }         |       '^' expr     %prec prREDUCTION       { $$ = new AstRedXor{$1, $2}; }         |       yP_NAND expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedAnd{$1, $2}}; }         |       yP_NOR  expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedOr{$1, $2}}; }         |       yP_XNOR expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedXor{$1, $2}}; }         |       inc_or_dec_expression                { $<fl>$ = $<fl>1; $$ = $1; }         |       '(' exprScope '='          expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, $4},                                                $2->cloneTreePure(true)};                           ASSIGNEQEXPR($<fl>3); }         |       '(' exprScope yP_PLUSEQ    expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAdd{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_MINUSEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstSub{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_TIMESEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstMul{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_DIVEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstDiv{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_MODEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstModDiv{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_ANDEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAnd{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_OREQ      expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstOr{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_XOREQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstXor{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_SLEFTEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftL{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_SRIGHTEQ  expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftR{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' exprScope yP_SSRIGHTEQ expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftRS{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       expr '+' expr                     { $$ = new AstAdd{$2, $1, $3}; }         |       expr '-' expr                     { $$ = new AstSub{$2, $1, $3}; }         |       expr '*' expr                     { $$ = new AstMul{$2, $1, $3}; }         |       expr '/' expr                     { $$ = new AstDiv{$2, $1, $3}; }         |       expr '%' expr                     { $$ = new AstModDiv{$2, $1, $3}; }         |       expr yP_EQUAL expr                { $$ = new AstEq{$2, $1, $3}; }         |       expr yP_NOTEQUAL expr             { $$ = new AstNeq{$2, $1, $3}; }         |       expr yP_CASEEQUAL expr            { $$ = new AstEqCase{$2, $1, $3}; }         |       expr yP_CASENOTEQUAL expr         { $$ = new AstNeqCase{$2, $1, $3}; }         |       expr yP_WILDEQUAL expr            { $$ = new AstEqWild{$2, $1, $3}; }         |       expr yP_WILDNOTEQUAL expr         { $$ = new AstNeqWild{$2, $1, $3}; }         |       expr yP_ANDAND expr               { $$ = new AstLogAnd{$2, $1, $3}; }         |       expr yP_OROR expr                 { $$ = new AstLogOr{$2, $1, $3}; }         |       expr yP_POW expr                  { $$ = new AstPow{$2, $1, $3}; }         |       expr '<' expr                     { $$ = new AstLt{$2, $1, $3}; }         |       expr '>' expr                     { $$ = new AstGt{$2, $1, $3}; }         |       expr yP_GTE expr                  { $$ = new AstGte{$2, $1, $3}; }         |       expr '&' expr                     { $$ = new AstAnd{$2, $1, $3}; }         |       expr '|' expr                     { $$ = new AstOr{$2, $1, $3}; }         |       expr '^' expr                     { $$ = new AstXor{$2, $1, $3}; }         |       expr yP_XNOR expr                 { $$ = new AstNot{$2, new AstXor{$2, $1, $3}}; }         |       expr yP_NOR expr                  { $$ = new AstNot{$2, new AstOr{$2, $1, $3}}; }         |       expr yP_NAND expr                 { $$ = new AstNot{$2, new AstAnd{$2, $1, $3}}; }         |       expr yP_SLEFT expr                { $$ = new AstShiftL{$2, $1, $3}; }         |       expr yP_SRIGHT expr               { $$ = new AstShiftR{$2, $1, $3}; }         |       expr yP_SSRIGHT expr              { $$ = new AstShiftRS{$2, $1, $3}; }         |       expr yP_LTMINUSGT expr            { $$ = new AstLogEq{$2, $1, $3}; }         |       type_referenceEq yP_CASEEQUAL type_referenceBoth     { $$ = new AstEqT{$2, $1, $3}; }         |       type_referenceEq yP_CASENOTEQUAL type_referenceBoth  { $$ = new AstNeqT{$2, $1, $3}; }         |       type_referenceEq yP_EQUAL type_referenceBoth         { $$ = new AstEqT{$2, $1, $3}; }         |       type_referenceEq yP_NOTEQUAL type_referenceBoth      { $$ = new AstNeqT{$2, $1, $3}; }         |       expr yP_MINUSGT expr              { $$ = new AstLogIf{$2, $1, $3}; }         |       expr yP_LTE expr       { $$ = new AstLte{$2, $1, $3}; }         |       expr '?' expr ':' expr         { $$ = new AstCond{$2, $1, $3, $5}; }         |       expr yINSIDE '{' range_list '}'      { $$ = new AstInside{$2, $1, $4}; }         |       yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }         |       yaFLOATNUM                              { $$ = new AstConst{$<fl>1, AstConst::RealDouble{}, $1}; }         |       timeNumAdjusted                         { $$ = $1; }         |       strAsIntIgnore                 { $$ = $1; }         |       '{' '}'                                 { $$ = new AstEmptyQueue{$1}; }         |       '{' constExpr '{' cateList '}' '}'                         { $$ = new AstReplicate{$3, $4, $2}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr ']'                         { $$ = new AstSelBit{$7, new AstReplicate{$3, $4, $2}, $8}; }         |       '{' constExpr '{' cateList '}' '}' '[' constExpr ':' constExpr ']'                         { $$ = new AstSelExtract{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr yP_PLUSCOLON constExpr ']'                         { $$ = new AstSelPlus{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr yP_MINUSCOLON constExpr ']'                         { $$ = new AstSelMinus{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       function_subroutine_callNoMethod                         { $$ = $1; }         |       function_subroutine_callNoMethod part_select_rangeList                         { $$ = GRAMMARP->scrubSel($1, $2); }         |       expr '.' function_subroutine_callNoMethod                         { $$ = new AstDot{$2, false, $1, $3}; }         |       expr '.' function_subroutine_callNoMethod part_select_rangeList                         { $$ = GRAMMARP->scrubSel(new AstDot{$2, false, $1, $3}, $4); }         |       expr '.' array_methodWith                         { $$ = new AstDot{$2, false, $1, $3}; }         |       expr '.' array_methodWith part_select_rangeList                         { $$ = GRAMMARP->scrubSel(new AstDot{$2, false, $1, $3}, $4); }         |       '(' expr ')'             { $$ = $2; }         |       '(' expr ':' expr ':' expr ')'                         { $$ = $4; MINTYPMAXDLYUNSUP($4); DEL($2); DEL($6); }         |       '_' '(' expr ')'                        { $$ = $3; }         |       simple_typeNoRef yP_TICK '(' expr ')'                         { $$ = new AstCast{$2, $4, VFlagChildDType{}, $1}; }         |       yTYPE__ETC '(' exprOrDataType ')' yP_TICK '(' expr ')'                         { $$ = new AstCast{$1, $7, VFlagChildDType{},                                            new AstRefDType{$1, AstRefDType::FlagTypeOfExpr{}, $3}}; }         |       ySIGNED yP_TICK '(' expr ')'            { $$ = new AstSigned{$1, $4}; }         |       yUNSIGNED yP_TICK '(' expr ')'          { $$ = new AstUnsigned{$1, $4}; }         |       ySTRING yP_TICK '(' expr ')'            { $$ = new AstCvtPackString{$1, $4}; }         |       yCONST__ETC yP_TICK '(' expr ')'        { $$ = $4; }         |       expr yP_TICK '(' expr ')'            { $$ = new AstCastParse{$2, $4, $1}; }         |       '$'                                     { $$ = new AstUnbounded{$<fl>1}; }         |       yNULL                                   { $$ = new AstConst{$1, AstConst::Null{}}; }         |       exprOkLvalue                         { $$ = $1; }         |       expr yP_ANDANDAND expr            { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: &&& expression"); }         |       expr yMATCHES patternNoExpr          { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: matches operator"); }         |       expr yMATCHES expr                { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: matches operator"); }         |       expr yDIST '{' dist_list '}'         { $$ = new AstDist{$2, $1, $4}; }        // {copied}
        ;

exprOkLvalue:            // expression that's also OK to use as a variable_lvalue
                exprScope                            { $$ = $1; }
        //                      // IEEE: concatenation/constant_concatenation
        //                      // Replicate(1) required as otherwise "{a}" would not be self-determined
        |       '{' cateList '}'                        { $$ = new AstReplicate{$1, $2, 1}; }
        |       '{' cateList '}' '[' expr ']'           { $$ = new AstSelBit{$4, new AstReplicate{$1, $2, 1}, $5}; }
        |       '{' cateList '}' '[' constExpr ':' constExpr ']'
                                                        { $$ = new AstSelExtract{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }
        |       '{' cateList '}' '[' expr yP_PLUSCOLON constExpr ']'
                                                        { $$ = new AstSelPlus{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }
        |       '{' cateList '}' '[' expr yP_MINUSCOLON constExpr ']'
                                                        { $$ = new AstSelMinus{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }
        //                      // IEEE: assignment_pattern_expression
        //                      // IEEE: [ assignment_pattern_expression_type ] == [ ps_type_id /ps_paremeter_id/data_type]
        //                      // We allow more here than the spec requires
        //UNSUP exprScope assignment_pattern         { UNSUP }
        |       data_type assignment_pattern            { $$ = $2; if ($2) $2->childDTypep($1); }
        |       assignment_pattern                      { $$ = $1; }
        //
        |       streaming_concatenation                 { $$ = $1; }
        ;

fexprOkLvalue:           // exprOkLValue, For use as first part of statement (disambiguates <=)
                                 fexprScope                            { $$ = $1; }         |       '{' cateList '}'                        { $$ = new AstReplicate{$1, $2, 1}; }         |       '{' cateList '}' '[' expr ']'           { $$ = new AstSelBit{$4, new AstReplicate{$1, $2, 1}, $5}; }         |       '{' cateList '}' '[' constExpr ':' constExpr ']'                                                         { $$ = new AstSelExtract{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }         |       '{' cateList '}' '[' expr yP_PLUSCOLON constExpr ']'                                                         { $$ = new AstSelPlus{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }         |       '{' cateList '}' '[' expr yP_MINUSCOLON constExpr ']'                                                         { $$ = new AstSelMinus{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }         |       data_type assignment_pattern            { $$ = $2; if ($2) $2->childDTypep($1); }         |       assignment_pattern                      { $$ = $1; }         |       streaming_concatenation                 { $$ = $1; }  // {copied}
        ;

sexprOkLvalue:  // exprOkLValue, For use by sequence_expr
                                 sexprScope                            { $$ = $1; }         |       '{' cateList '}'                        { $$ = new AstReplicate{$1, $2, 1}; }         |       '{' cateList '}' '[' expr ']'           { $$ = new AstSelBit{$4, new AstReplicate{$1, $2, 1}, $5}; }         |       '{' cateList '}' '[' constExpr ':' constExpr ']'                                                         { $$ = new AstSelExtract{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }         |       '{' cateList '}' '[' expr yP_PLUSCOLON constExpr ']'                                                         { $$ = new AstSelPlus{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }         |       '{' cateList '}' '[' expr yP_MINUSCOLON constExpr ']'                                                         { $$ = new AstSelMinus{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }         |       data_type assignment_pattern            { $$ = $2; if ($2) $2->childDTypep($1); }         |       assignment_pattern                      { $$ = $1; }         |       streaming_concatenation                 { $$ = $1; }  // {copied}
        ;

pexprOkLvalue:  // exprOkLValue, For use by property_expr
                                 pexprScope                            { $$ = $1; }         |       '{' cateList '}'                        { $$ = new AstReplicate{$1, $2, 1}; }         |       '{' cateList '}' '[' expr ']'           { $$ = new AstSelBit{$4, new AstReplicate{$1, $2, 1}, $5}; }         |       '{' cateList '}' '[' constExpr ':' constExpr ']'                                                         { $$ = new AstSelExtract{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }         |       '{' cateList '}' '[' expr yP_PLUSCOLON constExpr ']'                                                         { $$ = new AstSelPlus{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }         |       '{' cateList '}' '[' expr yP_MINUSCOLON constExpr ']'                                                         { $$ = new AstSelMinus{$4, new AstReplicate{$1, $2, 1}, $5, $7}; }         |       data_type assignment_pattern            { $$ = $2; if ($2) $2->childDTypep($1); }         |       assignment_pattern                      { $$ = $1; }         |       streaming_concatenation                 { $$ = $1; }  // {copied}
        ;

//UNSUPev_exprOkLvalue<nodeExprp>:  // exprOkLValue, For use by ev_expr
//UNSUP         BISONPRE_COPY(exprOkLvalue,{s//ev_/g})       // {copied}
//UNSUP ;

//UNSUPpev_exprOkLvalue<nodeExprp>:  // exprOkLValue, For use by ev_expr
//UNSUP         BISONPRE_COPY(exprOkLvalue,{s//pev_/g})      // {copied}
//UNSUP ;

fexprLvalue:             // For use as first part of statement (disambiguates <=)
                fexprOkLvalue                           { $<fl>$ = $<fl>1; $$ = $1; }
        ;

exprScope:               // scope and variable for use to inside an expression
        //                      // Here we've split method_call_root | implicit_class_handle | class_scope | package_scope
        //                      // from the object being called and let expr's "." deal with resolving it.
        //                      // (note method_call_root was simplified to require a primary in 1800-2009)
        //
        //                      // IEEE: [ implicit_class_handle . | class_scope | package_scope ] hierarchical_identifier select
        //                      // Or method_call_body without parenthesis
        //                      // See also varRefClassBit, which is the non-expr version of most of this
                yTHIS                                   { $$ = new AstParseRef{$<fl>1, "this"}; }
        |       yD_ROOT                                 { $$ = new AstParseRef{$<fl>1, "$root"}; }
        |       idArrayed                               { $$ = $1; }
        |       packageClassScope idArrayed             { $$ = AstDot::newIfPkg($2->fileline(), $1, $2); }
        |       expr '.' idArrayed                   { $$ = new AstDot{$<fl>2, false, $1, $3}; }
        //                      // expr below must be a "yTHIS"
        |       expr '.' ySUPER
                        { AstParseRef* const anodep = VN_CAST($1, ParseRef);
                          if (anodep && anodep->name() == "this") {
                              $$ = new AstParseRef{$<fl>1, "super"};
                              $1->deleteTree();
                          } else {
                              $$ = $1;  $$->v3error("Syntax error: 'super' must be first name component, or after 'this.'");
                          }
                        }
        //                      // Part of implicit_class_handle
        |       ySUPER                                  { $$ = new AstParseRef{$<fl>1, "super"}; }
        ;

fexprScope:              // exprScope, For use as first part of statement (disambiguates <=)
                                 yTHIS                                   { $$ = new AstParseRef{$<fl>1, "this"}; }         |       yD_ROOT                                 { $$ = new AstParseRef{$<fl>1, "$root"}; }         |       idArrayed                               { $$ = $1; }         |       packageClassScope idArrayed             { $$ = AstDot::newIfPkg($2->fileline(), $1, $2); }         |       fexpr '.' idArrayed                   { $$ = new AstDot{$<fl>2, false, $1, $3}; }         |       fexpr '.' ySUPER                         { AstParseRef* const anodep = VN_CAST($1, ParseRef);                           if (anodep && anodep->name() == "this") {                               $$ = new AstParseRef{$<fl>1, "super"};                               $1->deleteTree();                           } else {                               $$ = $1;  $$->v3error("Syntax error: 'super' must be first name component, or after 'this.'");                           }                         }         |       ySUPER                                  { $$ = new AstParseRef{$<fl>1, "super"}; }     // {copied}
        ;

sexprScope:  // exprScope, For use by sequence_expr
                                 yTHIS                                   { $$ = new AstParseRef{$<fl>1, "this"}; }         |       yD_ROOT                                 { $$ = new AstParseRef{$<fl>1, "$root"}; }         |       idArrayed                               { $$ = $1; }         |       packageClassScope idArrayed             { $$ = AstDot::newIfPkg($2->fileline(), $1, $2); }         |       sexpr '.' idArrayed                   { $$ = new AstDot{$<fl>2, false, $1, $3}; }         |       sexpr '.' ySUPER                         { AstParseRef* const anodep = VN_CAST($1, ParseRef);                           if (anodep && anodep->name() == "this") {                               $$ = new AstParseRef{$<fl>1, "super"};                               $1->deleteTree();                           } else {                               $$ = $1;  $$->v3error("Syntax error: 'super' must be first name component, or after 'this.'");                           }                         }         |       ySUPER                                  { $$ = new AstParseRef{$<fl>1, "super"}; }     // {copied}
        ;

pexprScope:  // exprScope, For use by property_expr
                                 yTHIS                                   { $$ = new AstParseRef{$<fl>1, "this"}; }         |       yD_ROOT                                 { $$ = new AstParseRef{$<fl>1, "$root"}; }         |       idArrayed                               { $$ = $1; }         |       packageClassScope idArrayed             { $$ = AstDot::newIfPkg($2->fileline(), $1, $2); }         |       pexpr '.' idArrayed                   { $$ = new AstDot{$<fl>2, false, $1, $3}; }         |       pexpr '.' ySUPER                         { AstParseRef* const anodep = VN_CAST($1, ParseRef);                           if (anodep && anodep->name() == "this") {                               $$ = new AstParseRef{$<fl>1, "super"};                               $1->deleteTree();                           } else {                               $$ = $1;  $$->v3error("Syntax error: 'super' must be first name component, or after 'this.'");                           }                         }         |       ySUPER                                  { $$ = new AstParseRef{$<fl>1, "super"}; }     // {copied}
        ;

//UNSUPev_exprScope<nodeExprp>:  // exprScope, For use by ev_expr
//UNSUP         BISONPRE_COPY(exprScope,{s//ev_/g})  // {copied}
//UNSUP ;

//UNSUPpev_exprScope<nodeExprp>:  // exprScope, For use by ev_expr
//UNSUP         BISONPRE_COPY(exprScope,{s//pev_/g}) // {copied}
//UNSUP ;

// PLI calls exclude "" as integers, they're strings
// For $c("foo","bar") we want "bar" as a string, not a Verilog integer.
exprStrText:
                exprNoStr                               { $$ = $1; }
        |       yaSTRING                                { $$ = new AstText{$<fl>1, GRAMMARP->textQuoted($<fl>1, *$1)}; }
        ;

exprTypeCompare:
                expr                                    { $$ = $1; }
        |       type_referenceBoth                      { $$ = $1; }
        ;

cStrList:
                exprStrText                             { $$ = $1; }
        |       exprStrText ',' cStrList                { $$ = $1->addNext($3); }
        ;

cateList:
        //                      // Not just 'expr' to prevent conflict via stream_concOrExprOrType
                stream_expression                       { $$ = $1; }
        |       cateList ',' stream_expression          { $$ = new AstConcat{$2, $1, $3}; }
        ;

exprListE:
                /* empty */                             { $$ = nullptr; }
        |       exprList                                { $$ = $1; }
        ;

exprList:
                expr                                    { $$ = $1; }
        |       exprList ',' expr                       { $$ = $1->addNext($3); }
        ;

exprEListE:  // expression list with empty commas allowed
                exprE                                   { $$ = $1; }
        |       exprEListE ',' exprE                    { $$ = addNextNull($1, $3); }
        ;

exprDispList:            // exprList for within $display
                expr                                    { $$ = $1; }
        |       exprDispList ',' expr                   { $$ = $1->addNext($3); }
        //                      // ,, creates a space in $display
        |       exprDispList ',' /*empty*/
                        { $$ = $1->addNext(new AstConst{$<fl>2, AstConst::VerilogStringLiteral{}, " "}); }
        ;

vrdList:
                idClassSel                              { $$ = $1; }
        |       vrdList ',' idClassSel                  { $$ = $1->addNext($3); }
        ;

commasE:
                /* empty */                             { } /* ignored */
        |       ',' commasE                             { } /* ignored */
        ;

commaVRDListE:
                /* empty */                             { $$ = nullptr; }
        |       ',' vrdList                             { $$ = $2; }
        ;

argsExprList:        // IEEE: part of list_of_arguments (used where ,, isn't legal)
                expr                                    { $$ = $1; }
        |       argsExprList ',' expr                   { $$ = $1->addNext($3); }
        ;

argsExprListE:       // IEEE: part of list_of_arguments
                argsExprOneE                            { $$ = $1; }
        |       argsExprListE ',' argsExprOneE          { $$ = $1->addNext($3); }
        ;

//UNSUPpev_argsExprListE<nodeExprp>:  // IEEE: part of list_of_arguments - pev_expr at bottom
//UNSUP         pev_argsExprOneE                        { $$ = $1; }
//UNSUP |       pev_argsExprListE ',' pev_argsExprOneE  { $$ = addNextNull($1, $3); }
//UNSUP ;

argsExprOneE:        // IEEE: part of list_of_arguments
                /*empty*/                               { $$ = new AstArg{CRELINE(), "", nullptr}; }
        |       expr                                    { $$ = new AstArg{$1->fileline(), "", $1}; }
        ;

//UNSUPpev_argsExprOneE<nodeExprp>:  // IEEE: part of list_of_arguments - pev_expr at bottom
//UNSUP         /*empty*/                               { $$ = nullptr; }       // ,, is legal in list_of_arguments
//UNSUP |       pev_expr                                { $$ = $1; }
//UNSUP ;

argsDottedList:      // IEEE: part of list_of_arguments
                argsDotted                              { $$ = $1; }
        |       argsDottedList ',' argsDotted           { $$ = addNextNull($1, $3); }
        ;

//UNSUPpev_argsDottedList<nodeExprp>:  // IEEE: part of list_of_arguments - pev_expr at bottom
//UNSUP         pev_argsDotted                          { $$ = $1; }
//UNSUP |       pev_argsDottedList ',' pev_argsDotted   { $$ = addNextNull($1, $3); }
//UNSUP ;

argsDotted:          // IEEE: part of list_of_arguments
                '.' idAny '(' ')'                       { $$ = new AstArg{$<fl>2, *$2, nullptr}; }
        |       '.' idAny '(' expr ')'                  { $$ = new AstArg{$<fl>2, *$2, $4}; }
        ;

//UNSUPpev_argsDotted<nodeExprp>:  // IEEE: part of list_of_arguments - pev_expr at bottom
//UNSUP         '.' idAny '(' ')'                       { $$ = new AstArg{$<fl>2, *$2, nullptr}; }
//UNSUP |       '.' idAny '(' pev_expr ')'              { $$ = new AstArg{$<fl>2, *$2, $4}; }
//UNSUP ;

streaming_concatenation: // ==IEEE: streaming_concatenation
        //                      // Need to disambiguate {<< expr-{ ... expr-} stream_concat }
        //                      // From                 {<< stream-{ ... stream-} }
        //                      // Likewise simple_type's idScoped from constExpr's idScope
        //                      // Thus we allow always any two operations.  Sorry
        //                      // IEEE: "'{' yP_SL/R             stream_concatenation '}'"
        //                      // IEEE: "'{' yP_SL/R simple_type stream_concatenation '}'"
        //                      // IEEE: "'{' yP_SL/R constExpr   stream_concatenation '}'"
                '{' yP_SLEFT  stream_concatenation '}'
                        { $$ = new AstStreamL{$2, $3, new AstConst{$2, 1}}; }
        |       '{' yP_SRIGHT stream_concatenation '}'
                        { $$ = new AstStreamR{$2, $3, new AstConst{$2, 1}}; }
        |       '{' yP_SLEFT  stream_expressionOrDataType stream_concatenation '}'
                        { $$ = new AstStreamL{$2, $4, new AstAttrOf{$1, VAttrType::DIM_BITS_OR_NUMBER, $3}}; }
        |       '{' yP_SRIGHT stream_expressionOrDataType stream_concatenation '}'
                        { $$ = new AstStreamR{$2, $4, new AstAttrOf{$1, VAttrType::DIM_BITS_OR_NUMBER, $3}}; }
        ;

stream_concatenation:    // ==IEEE: stream_concatenation
        //                      // '{' { stream_expression } '}'
                '{' cateList '}'                        { $$ = $2; }
        ;

stream_expression:   // ==IEEE: stream_expression
        //                      // IEEE: array_range_expression expanded below
                expr                                    { $$ = $1; }
        |       expr yWITH__BRA '[' expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr ':' expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr yP_PLUSCOLON  expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr yP_MINUSCOLON expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        ;

stream_expressionOrDataType:     // IEEE: from streaming_concatenation
                exprOrDataType                          { $$ = $1; }
        |       expr yWITH__BRA '[' expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr ':' expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr yP_PLUSCOLON  expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        |       expr yWITH__BRA '[' expr yP_MINUSCOLON expr ']'
                        { $$ = $1; BBUNSUP($2, "Unsupported: with[] stream expression"); }
        ;

//************************************************
// Let

letId:  // IEEE: pert of let_declaration
                idAny/*let_identifieer*/
                        { $<fl>$ = $<fl>1;
                          $$ = new AstLet{$<fl>$, *$1}; }
        ;

let_declaration:  // IEEE: let_declaration
                yLET letId '=' expr ';'
                        { $$ = $2;
                          $$->addStmtsp(new AstStmtExpr{$1, $4}); }
        |       yLET letId '(' let_port_listE ')' '=' expr ';'
                        { $$ = $2;
                          $$->addStmtsp(new AstStmtExpr{$1, $7});
                          $$->addStmtsp($4); }
        ;

let_port_listE:   // IEEE: [ let_port_list ]
                /*empty*/                               { $$ = nullptr; }
        |       /*emptyStart*/
        /*mid*/         { VARRESET_LIST(VAR); VARIO(INOUT); }
        /*cont*/  let_port_list                         { $$ = $2; VARRESET_NONLIST(UNKNOWN); }
        ;

let_port_list:   // IEEE: let_port_list
                let_port_item                           { $$ = $1; }
        |       let_port_list ',' let_port_item         { $$ = addNextNull($1, $3); }
        ;

let_port_item:  // IEEE: let_port_Item
        //                      // IEEE: Expanded let_formal_type
                yUNTYPED idAny/*formal_port_identifier*/ variable_dimensionListE exprEqE
                        { $$ = new AstVar{$<fl>2, VVarType::VAR, *$2, VFlagChildDType{},
                                          new AstBasicDType{$<fl>2, LOGIC_IMPLICIT}};
                          $$->direction(VDirection::INOUT);
                          $$->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                          if ($4) $$->valuep($4);
                          PINNUMINC(); }
        |       data_type idAny/*formal_port_identifier*/ variable_dimensionListE exprEqE
                        { BBUNSUP($<fl>1, "Unsupported: let typed ports");
                          $$ = new AstVar{$<fl>2, VVarType::VAR, *$2, VFlagChildDType{},
                                          new AstBasicDType{$<fl>2, LOGIC_IMPLICIT}};
                          $$->direction(VDirection::INOUT);
                          $$->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                          if ($4) $$->valuep($4);
                          PINNUMINC(); }
        |       implicit_typeE id/*formal_port_identifier*/ variable_dimensionListE exprEqE
                        { if ($1) BBUNSUP($<fl>1, "Unsupported: let typed ports");
                          $$ = new AstVar{$<fl>2, VVarType::VAR, *$2, VFlagChildDType{},
                                          new AstBasicDType{$<fl>2, LOGIC_IMPLICIT}};
                          $$->direction(VDirection::INOUT);
                          $$->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                          if ($4) $$->valuep($4);
                          PINNUMINC(); }
        ;

//************************************************
// Gate declarations

gateDecl:
                yBUF    driveStrengthE delay_controlE gateBufList ';'     { $$ = $4; STRENGTHUNSUP($2);     DELAY_LIST($4, $3); }
        |       yBUFIF0 driveStrengthE delay_controlE gateBufif0List ';'  { $$ = $4; STRENGTHUNSUP($2);     DELAY_LIST($4, $3); }
        |       yBUFIF1 driveStrengthE delay_controlE gateBufif1List ';'  { $$ = $4; STRENGTHUNSUP($2);     DELAY_LIST($4, $3); }
        |       yNOT    driveStrengthE delay_controlE gateNotList ';'     { $$ = $4; STRENGTH_LIST($4, $2); DELAY_LIST($4, $3); }
        |       yNOTIF0 driveStrengthE delay_controlE gateNotif0List ';'  { $$ = $4; STRENGTHUNSUP($2);     DELAY_LIST($4, $3); }
        |       yNOTIF1 driveStrengthE delay_controlE gateNotif1List ';'  { $$ = $4; STRENGTHUNSUP($2);     DELAY_LIST($4, $3); }
        |       yAND    driveStrengthE delay_controlE gateAndList ';'     { $$ = $4; STRENGTH_LIST($4, $2); DELAY_LIST($4, $3); }
        |       yNAND   driveStrengthE delay_controlE gateNandList ';'    { $$ = $4; STRENGTH_LIST($4, $2); DELAY_LIST($4, $3); }
        |       yOR     driveStrengthE delay_controlE gateOrList ';'      { $$ = $4; STRENGTH_LIST($4, $2); DELAY_LIST($4, $3); }
        |       yNOR    driveStrengthE delay_controlE gateNorList ';'     { $$ = $4; STRENGTH_LIST($4, $2); DELAY_LIST($4, $3); }
        |       yXOR    driveStrengthE delay_controlE gateXorList ';'     { $$ = $4; STRENGTH_LIST($4, $2); DELAY_LIST($4, $3); }
        |       yXNOR   driveStrengthE delay_controlE gateXnorList ';'    { $$ = $4; STRENGTH_LIST($4, $2); DELAY_LIST($4, $3); }
        |       yPULLDOWN pulldown_strengthE delay_controlE gatePulldownList ';'   { $$ = $4; DELAY_LIST($4, $3); }
        |       yPULLUP   pullup_strengthE   delay_controlE gatePullupList ';'     { $$ = $4; DELAY_LIST($4, $3); }
        |       yNMOS     delay_controlE gateBufif1List ';'     { $$ = $3; DELAY_LIST($3, $2); }
        |       yPMOS     delay_controlE gateBufif0List ';'     { $$ = $3; DELAY_LIST($3, $2); }
        //
        |       yTRAN delay_controlE gateUnsupList ';'          { $$ = $3; GATEUNSUP($3, "tran"); }
        |       yRCMOS delay_controlE gateUnsupList ';'         { $$ = $3; GATEUNSUP($3, "rcmos"); }
        |       yCMOS delay_controlE gateUnsupList ';'          { $$ = $3; GATEUNSUP($3, "cmos"); }
        |       yRNMOS delay_controlE gateUnsupList ';'         { $$ = $3; GATEUNSUP($3, "rmos"); }
        |       yRPMOS delay_controlE gateUnsupList ';'         { $$ = $3; GATEUNSUP($3, "pmos"); }
        |       yRTRAN delay_controlE gateUnsupList ';'         { $$ = $3; GATEUNSUP($3, "rtran"); }
        |       yRTRANIF0 delay_controlE gateUnsupList ';'      { $$ = $3; GATEUNSUP($3, "rtranif0"); }
        |       yRTRANIF1 delay_controlE gateUnsupList ';'      { $$ = $3; GATEUNSUP($3, "rtranif1"); }
        |       yTRANIF0 delay_controlE gateUnsupList ';'       { $$ = $3; GATEUNSUP($3, "tranif0"); }
        |       yTRANIF1 delay_controlE gateUnsupList ';'       { $$ = $3; GATEUNSUP($3, "tranif1"); }
        ;

gateBufList:
                gateBuf                                 { $$ = $1; }
        |       gateBufList ',' gateBuf                 { $$ = $1->addNext($3); }
        ;
gateBufif0List:
                gateBufif0                              { $$ = $1; }
        |       gateBufif0List ',' gateBufif0           { $$ = $1->addNext($3); }
        ;
gateBufif1List:
                gateBufif1                              { $$ = $1; }
        |       gateBufif1List ',' gateBufif1           { $$ = $1->addNext($3); }
        ;
gateNotList:
                gateNot                                 { $$ = $1; }
        |       gateNotList ',' gateNot                 { $$ = $1->addNext($3); }
        ;
gateNotif0List:
                gateNotif0                              { $$ = $1; }
        |       gateNotif0List ',' gateNotif0           { $$ = $1->addNext($3); }
        ;
gateNotif1List:
                gateNotif1                              { $$ = $1; }
        |       gateNotif1List ',' gateNotif1           { $$ = $1->addNext($3); }
        ;
gateAndList:
                gateAnd                                 { $$ = $1; }
        |       gateAndList ',' gateAnd                 { $$ = $1->addNext($3); }
        ;
gateNandList:
                gateNand                                { $$ = $1; }
        |       gateNandList ',' gateNand               { $$ = $1->addNext($3); }
        ;
gateOrList:
                gateOr                                  { $$ = $1; }
        |       gateOrList ',' gateOr                   { $$ = $1->addNext($3); }
        ;
gateNorList:
                gateNor                                 { $$ = $1; }
        |       gateNorList ',' gateNor                 { $$ = $1->addNext($3); }
        ;
gateXorList:
                gateXor                                 { $$ = $1; }
        |       gateXorList ',' gateXor                 { $$ = $1->addNext($3); }
        ;
gateXnorList:
                gateXnor                                { $$ = $1; }
        |       gateXnorList ',' gateXnor               { $$ = $1->addNext($3); }
        ;
gatePullupList:
                gatePullup                              { $$ = $1; }
        |       gatePullupList ',' gatePullup           { $$ = $1->addNext($3); }
        ;
gatePulldownList:
                gatePulldown                            { $$ = $1; }
        |       gatePulldownList ',' gatePulldown       { $$ = $1->addNext($3); }
        ;
gateUnsupList:
                gateUnsup                               { $$ = $1; }
        |       gateUnsupList ',' gateUnsup             { $$ = $1->addNext($3); }
        ;

gateRangeE:
                instRangeListE                          { $$ = $1; GATERANGE(GRAMMARP->scrubRange($1)); }
        ;

gateBuf:
                gateFront variable_lvalue ',' exprList ')'
                        { AstNodeExpr* inp = $4;
                          while (inp->nextp()) inp = VN_AS(inp->nextp(), NodeExpr);
                          $$ = new AstImplicit{$<fl>1, inp->cloneTree(false)};
                          AstNodeExpr* const rhsp = GRAMMARP->createGatePin(inp->cloneTree(false));
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          for (AstNodeExpr* outp = $4; outp->nextp(); outp = VN_CAST(outp->nextp(), NodeExpr)) {
                              AstNodeExpr* const pinRhsp = GRAMMARP->createGatePin(inp->cloneTree(false));
                              AstAssignW* const pinAssp = new AstAssignW{$<fl>1, outp->cloneTree(false), pinRhsp};
                              $$->addNext(new AstAlways{pinAssp});
                          }
                          DEL($1); DEL($4); }
        ;
gateNot:
                gateFront variable_lvalue ',' exprList ')'
                        { AstNodeExpr* inp = $4;
                          while (inp->nextp()) inp = VN_AS(inp->nextp(), NodeExpr);
                          $$ = new AstImplicit{$<fl>1, inp->cloneTree(false)};
                          AstNodeExpr* const rhsp = new AstNot{$<fl>1, GRAMMARP->createGatePin(inp->cloneTree(false))};
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          for (AstNodeExpr* outp = $4; outp->nextp(); outp = VN_CAST(outp->nextp(), NodeExpr)) {
                              AstNodeExpr* const pinRhsp = new AstNot{$<fl>1, GRAMMARP->createGatePin(inp->cloneTree(false))};
                              AstAssignW* const pinAssp = new AstAssignW{$<fl>1, outp->cloneTree(false), pinRhsp};
                              $$->addNext(new AstAlways{pinAssp});
                          }
                          DEL($1, $4); }
        ;
gateBufif0:
                gateFront variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
                        { $$ = new AstImplicit{$<fl>1, $6->cloneTree(false)};
                          $<implicitp>$->addExprsp($4->cloneTree(false));
                          AstNodeExpr* const rhsp = new AstBufIf1{$<fl>1, new AstNot{$<fl>1, $6}, $4};
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          DEL($1); }
        ;
gateBufif1:
                gateFront variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
                        { $$ = new AstImplicit{$<fl>1, $6->cloneTree(false)};
                          $<implicitp>$->addExprsp($4->cloneTree(false));
                          AstNodeExpr* const rhsp = new AstBufIf1{$<fl>1, $6, $4};
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          DEL($1); }
        ;
gateNotif0:
                gateFront variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
                        { $$ = new AstImplicit{$<fl>1, $6->cloneTree(false)};
                          $<implicitp>$->addExprsp($4->cloneTree(false));
                          AstNodeExpr* const rhsp = new AstBufIf1{$<fl>1, new AstNot{$<fl>1, $6}, new AstNot{$<fl>1, $4}};
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          DEL($1); }
        ;
gateNotif1:
                gateFront variable_lvalue ',' gatePinExpr ',' gatePinExpr ')'
                        { $$ = new AstImplicit{$<fl>1, $6->cloneTree(false)};
                          $<implicitp>$->addExprsp($4->cloneTree(false));
                          AstNodeExpr* const rhsp = new AstBufIf1{$<fl>1, $6, new AstNot{$<fl>1, $4}};
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          DEL($1); }
        ;
gateAnd:
                gateFront variable_lvalue ',' gateAndPinList ')'
                        { $$ = new AstImplicit{$<fl>1, $4->cloneTree(false)};
                          AstNodeExpr* const rhsp = $4;
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          DEL($1); }
        ;
gateNand:
                gateFront variable_lvalue ',' gateAndPinList ')'
                        { $$ = new AstImplicit{$<fl>1, $4->cloneTree(false)};
                          AstNodeExpr* const rhsp = new AstNot{$<fl>1, $4};
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          DEL($1); }
        ;
gateOr:
                gateFront variable_lvalue ',' gateOrPinList ')'
                        { $$ = new AstImplicit{$<fl>1, $4->cloneTree(false)};
                          AstNodeExpr* const rhsp = $4;
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          DEL($1); }
        ;
gateNor:
                gateFront variable_lvalue ',' gateOrPinList ')'
                        { $$ = new AstImplicit{$<fl>1, $4->cloneTree(false)};
                          AstNodeExpr* const rhsp = new AstNot{$<fl>1, $4};
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          DEL($1); }
        ;
gateXor:
                gateFront variable_lvalue ',' gateXorPinList ')'
                        { $$ = new AstImplicit{$<fl>1, $4->cloneTree(false)};
                          AstNodeExpr* const rhsp = $4;
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          DEL($1); }
        ;
gateXnor:
                gateFront variable_lvalue ',' gateXorPinList ')'
                        { $$ = new AstImplicit{$<fl>1, $4->cloneTree(false)};
                          AstNodeExpr* const rhsp = new AstNot{$<fl>1, $4};
                          AstAssignW* const ap = new AstAssignW{$<fl>1, $2, rhsp};
                          $$->addNext(new AstAlways{ap});
                          DEL($1); }
        ;
gatePullup:
                gateFront variable_lvalue ')'           { $$ = new AstPull{$<fl>1, $2, true}; DEL($1); }
        ;
gatePulldown:
                gateFront variable_lvalue ')'           { $$ = new AstPull{$<fl>1, $2, false}; DEL($1); }
        ;
gateUnsup:
                gateFront gateUnsupPinList ')'          { $$ = new AstImplicit{$<fl>1, $2}; DEL($1); }
        ;

gateFront:
                id/*gate*/ gateRangeE '('               { $$ = $2; $<fl>$ = $<fl>1; }
        |       gateRangeE '('                          { $$ = $1; $<fl>$ = $<fl>2; }
        ;

gateAndPinList:
                gatePinExpr                             { $$ = $1; }
        |       gateAndPinList ',' gatePinExpr          { $$ = new AstAnd{$2, $1, $3}; }
        ;
gateOrPinList:
                gatePinExpr                             { $$ = $1; }
        |       gateOrPinList ',' gatePinExpr           { $$ = new AstOr{$2, $1, $3}; }
        ;
gateXorPinList:
                gatePinExpr                             { $$ = $1; }
        |       gateXorPinList ',' gatePinExpr          { $$ = new AstXor{$2, $1, $3}; }
        ;
gateUnsupPinList:
                gatePinExpr                             { $$ = $1; }
        |       gateUnsupPinList ',' gatePinExpr        { $$ = addNextNull($1, $3); }
        ;

gatePinExpr:
                expr                                    { $$ = GRAMMARP->createGatePin($1); }
        ;

strength0:
                ySUPPLY0                                { $$ = VStrength::SUPPLY; }
        |       ySTRONG0                                { $$ = VStrength::STRONG; }
        |       yPULL0                                  { $$ = VStrength::PULL; }
        |       yWEAK0                                  { $$ = VStrength::WEAK; }
        ;

strength1:
                ySUPPLY1                                { $$ = VStrength::SUPPLY; }
        |       ySTRONG1                                { $$ = VStrength::STRONG; }
        |       yPULL1                                  { $$ = VStrength::PULL; }
        |       yWEAK1                                  { $$ = VStrength::WEAK; }
        ;

driveStrengthE:
                /* empty */                             { $$ = nullptr; }
        |       driveStrength                           { $$ = $1; }
        ;

driveStrength:
                yP_PAR__STRENGTH strength0 ',' strength1 ')' { $$ = new AstStrengthSpec{$1, $2, $4}; }
        |       yP_PAR__STRENGTH strength1 ',' strength0 ')' { $$ = new AstStrengthSpec{$1, $4, $2}; }
        |       yP_PAR__STRENGTH strength0 ',' yHIGHZ1 ')' { $$ = nullptr; BBUNSUP($<fl>4, "Unsupported: highz strength"); }
        |       yP_PAR__STRENGTH strength1 ',' yHIGHZ0 ')' { $$ = nullptr; BBUNSUP($<fl>4, "Unsupported: highz strength"); }
        |       yP_PAR__STRENGTH yHIGHZ0 ',' strength1 ')' { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: highz strength"); }
        |       yP_PAR__STRENGTH yHIGHZ1 ',' strength0 ')' { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: highz strength"); }
        ;

pulldown_strengthE:  // IEEE: [ pulldown_strength ]
                /* empty */                             { $$ = nullptr; }
        |       pulldown_strength                       { $$ = $1; }
        ;

pulldown_strength:  // IEEE: pulldown_strength
                yP_PAR__STRENGTH strength0 ',' strength1 ')'  { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: pulldown strength"); }
        |       yP_PAR__STRENGTH strength1 ',' strength0 ')'  { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: pulldown strength"); }
        |       yP_PAR__STRENGTH strength0 ')'                { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: pulldown strength"); }
        ;

pullup_strengthE:  // IEEE: [ pullup_strength ]
                /* empty */                             { $$ = nullptr; }
        |       pullup_strength                         { $$ = $1; }
        ;

pullup_strength:  // IEEE: pullup_strength
                yP_PAR__STRENGTH strength0 ',' strength1 ')'  { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: pullup strength"); }
        |       yP_PAR__STRENGTH strength1 ',' strength0 ')'  { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: pullup strength"); }
        |       yP_PAR__STRENGTH strength1 ')'                { $$ = nullptr; BBUNSUP($<fl>2, "Unsupported: pullup strength"); }
        ;

//************************************************
// Tables

combinational_body:      // IEEE: combinational_body + sequential_body
                yTABLE tableEntryList yENDTABLE         { $$ = new AstUdpTable{$1, $2}; }
        ;

tableEntryList:  // IEEE: { combinational_entry + sequential_entry }
                tableLine                              { $$ = $1; }
        |       tableEntryList tableLine               { $$ = addNextNull($1, $2); }
        ;

tableLine:
                tableInputList yaTABLE_LRSEP tablelVal yaTABLE_LINEEND
                        { $$ = new AstUdpTableLine{AstUdpTableLine::UdpCombo{}, $<fl>1, $1, $3}; }
        |       tableInputList yaTABLE_LRSEP tablelVal yaTABLE_LRSEP tablelVal yaTABLE_LINEEND
                        { $$ = new AstUdpTableLine{AstUdpTableLine::UdpSequential{}, $<fl>1, $1, $3, $5}; }
        ;

tableInputList:
                tablelVal                            { $$ = $1; }
        |       tableInputList tablelVal             { $$ = addNextNull($1, $2); }
        ;

tablelVal:
                yaTABLE_FIELD                          { $$ = new AstUdpTableLineVal{$<fl>1, *$1}; }
        |       '(' yaTABLE_FIELD yaTABLE_FIELD ')'    { $$ = new AstUdpTableLineVal{$<fl>2, *$2 + *$3}; }
        ;

//************************************************
// Specify

specify_block:               // ==IEEE: specify_block
                specifyFront specify_itemList yENDSPECIFY   { $$ = $2; }
        |       specifyFront yENDSPECIFY                { $$ = nullptr; }
        ;

specifyFront:  // IEEE: specify_block front
                ySPECIFY                                { GRAMMARP->m_specifyignWarned = false; }
        ;

specify_itemList:            // IEEE: { specify_item }
                specify_item                            { $$ = $1; }
        |       specify_itemList specify_item           { $$ = addNextNull($1, $2); }
        ;

specify_item:                // ==IEEE: specify_item
                specparam_declaration                   { $$ = $1; }
        |       system_timing_check                     { $$ = $1; }
        |       junkToSemiList ';'
                        { $$ = nullptr;
                          if (!GRAMMARP->m_specifyignWarned) {
                              GRAMMARP->m_specifyignWarned = true;
                              $1->v3warn(SPECIFYIGN, "Ignoring unsupported: specify block construct");
                          }
                        }
        ;

specparam_declaration:       // ==IEEE: specparam_declaration
                specparam_declarationFront list_of_specparam_assignments ';'
                        { $$ = $2; }
        ;

specparam_declarationFront:     // IEEE: part of specparam_declaration
        //                      // Front must execute first so VARDTYPE is ready before list of vars
                ySPECPARAM
                        { VARRESET_NONLIST(SPECPARAM);
                          AstNodeDType* dtp = new AstBasicDType{$1, VBasicDTypeKwd::DOUBLE};
                          VARDTYPE(dtp); }
        |       ySPECPARAM packed_dimension
                        { VARRESET_NONLIST(SPECPARAM);
                          AstNodeDType* const dtp = GRAMMARP->addRange(
                                    new AstBasicDType{$2->fileline(), LOGIC_IMPLICIT}, $2, true);
                          VARDTYPE(dtp); }
        ;

list_of_specparam_assignments:  // ==IEEE: list_of_specparam_assignments
                specparam_assignment                    { $$ = $1; }
        |       list_of_specparam_assignments ',' specparam_assignment  { $$ = $1->addNext($3); }
        ;

specparam_assignment:     // ==IEEE: specparam_assignment
                idNotPathpulse sigAttrListE '=' minTypMax
                        { $$ = VARDONEA($<fl>1, *$1, nullptr, $2);
                          if ($4) $$->valuep($4); }
        //                      //  IEEE: pulse_control_specparam
        |       idPathpulse sigAttrListE '=' '(' minTypMax ')'
                        { $$ = VARDONEA($<fl>1, *$1, nullptr, $2);
                          if ($5) $$->valuep($5); }
        |       idPathpulse sigAttrListE '=' '(' minTypMax ',' minTypMax ')'
                        { $$ = VARDONEA($<fl>1, *$1, nullptr, $2);
                          if ($5) $$->valuep($5);
                          DEL($7); }
        ;

system_timing_check:         // ==IEEE: system_timing_check
                setuphold_timing_check                      { $$ = $1; }
        ;

setuphold_timing_check:      // ==IEEE: $setuphold_timing_check
                yD_SETUPHOLD '(' timing_check_event ',' timing_check_event ',' timing_check_limit ',' timing_check_limit ')' ';'
                        { $$ = nullptr; DEL($3, $5, $7, $9); }
        |       yD_SETUPHOLD '(' timing_check_event ',' timing_check_event ',' timing_check_limit ',' timing_check_limit ',' idAnyE ')' ';'
                        { $$ = nullptr; DEL($3, $5, $7, $9); }
        |       yD_SETUPHOLD '(' timing_check_event ',' timing_check_event ',' timing_check_limit ',' timing_check_limit ',' idAnyE ',' minTypMaxE ')' ';'
                        { $$ = nullptr; DEL($3, $5, $7, $9, $13); }
        |       yD_SETUPHOLD '(' timing_check_event ',' timing_check_event ',' timing_check_limit ',' timing_check_limit ',' idAnyE ',' minTypMaxE ',' minTypMaxE ')' ';'
                        { $$ = nullptr; DEL($3, $5, $7, $9, $13, $15); }
        |       yD_SETUPHOLD '(' timing_check_event ',' timing_check_event ',' timing_check_limit ',' timing_check_limit ',' idAnyE ',' minTypMaxE ',' minTypMaxE ',' delayed_referenceE ')' ';'
                        { $$ = new AstSetuphold{$1, $3, $5, $17}; DEL($7, $9, $13, $15);  }
        |       yD_SETUPHOLD '(' timing_check_event ',' timing_check_event ',' timing_check_limit ',' timing_check_limit ',' idAnyE ',' minTypMaxE ',' minTypMaxE ',' delayed_referenceE ',' delayed_referenceE ')' ';'
                        { $$ = new AstSetuphold{$1, $3, $5, $17, $19}; DEL($7, $9, $13, $15); }
        ;

timing_check_event:      // ==IEEE: $timing_check_event
                terminal_identifier                                                         { $$ = $1; }
        |       yPOSEDGE terminal_identifier                                                { $$ = $2; }
        |       yNEGEDGE terminal_identifier                                                { $$ = $2; }
        |       yEDGE terminal_identifier                                                   { $$ = $2; }
        |       yEDGE '[' edge_descriptor_list ']' terminal_identifier                      { $$ = $5; }
        |       terminal_identifier yP_ANDANDAND expr                                       { $$ = $1; DEL($3); }
        |       yPOSEDGE terminal_identifier yP_ANDANDAND expr                              { $$ = $2; DEL($4); }
        |       yNEGEDGE terminal_identifier yP_ANDANDAND expr                              { $$ = $2; DEL($4); }
        |       yEDGE terminal_identifier yP_ANDANDAND expr                                 { $$ = $2; DEL($4); }
        |       yEDGE '[' edge_descriptor_list ']' terminal_identifier yP_ANDANDAND expr    { $$ = $5; DEL($7); }
        ;

edge_descriptor_list:
                yaEDGEDESC                            {  }
        |       edge_descriptor_list ',' yaEDGEDESC   {  }
        ;

timing_check_limit:
                expr                      { $$ = $1; }
        |       expr ':' expr ':' expr    { $$ = $3; DEL($1, $5); }
        ;

delayed_referenceE:
                /*empty*/                               { $$ = nullptr; }
        |       terminal_identifier                     { $$ = $1; }
        ;

terminal_identifier:
                idArrayed     { $$ = $1; }
        ;

idAnyE:
                /*empty*/                               { $$ = nullptr; }
        |       idAny                                   { $$ = $1; }
        ;

junkToSemiList:
                junkToSemi                              { $$ = CRELINE(); }
        |       junkToSemiList junkToSemi               { $$ = CRELINE(); }
        ;

junkToSemi:
                	 '!' { }	| '#' { }	| '%' { }	| '&' { }	| '(' { }	| ')' { }	| '*' { }	| '+' { }	| ',' { }	| '-' { }	| '.' { }	| '/' { }	| ':' { }	| '<' { }	| '=' { }	| '>' { }	| '?' { }	| '@' { }	| '[' { }	| ']' { }	| '^' { }	| '{' { }	| '|' { }	| '}' { }	| '~' { }	| prTAGGED { }	| y1STEP { }	| yACCEPT_ON { }	| yALIAS { }	| yALWAYS { }	| yALWAYS_COMB { }	| yALWAYS_FF { }	| yALWAYS_LATCH { }	| yAND { }	| yASSERT { }	| yASSIGN { }	| yASSUME { }	| yAUTOMATIC { }	| yBEFORE { }	| yBEGIN { }	| yBIND { }	| yBINS { }	| yBINSOF { }	| yBIT { }	| yBREAK { }	| yBUF { }	| yBUFIF0 { }	| yBUFIF1 { }	| yBYTE { }	| yCASE { }	| yCASEX { }	| yCASEZ { }	| yCELL { }	| yCHANDLE { }	| yCHECKER { }	| yCLASS { }	| yCLOCKING { }	| yCMOS { }	| yCONFIG { }	| yCONSTRAINT { }	| yCONST__ETC { }	| yCONST__LEX { }	| yCONST__REF { }	| yCONTEXT { }	| yCONTINUE { }	| yCOVER { }	| yCOVERGROUP { }	| yCOVERPOINT { }	| yCROSS { }	| yDEASSIGN { }	| yDEFAULT { }	| yDEFPARAM { }	| yDESIGN { }	| yDISABLE { }	| yDIST { }	| yDO { }	| yD_ACOS { }	| yD_ACOSH { }	| yD_ASIN { }	| yD_ASINH { }	| yD_ASSERTCTL { }	| yD_ASSERTFAILOFF { }	| yD_ASSERTFAILON { }	| yD_ASSERTKILL { }	| yD_ASSERTNONVACUOUSON { }	| yD_ASSERTOFF { }	| yD_ASSERTON { }	| yD_ASSERTPASSOFF { }	| yD_ASSERTPASSON { }	| yD_ASSERTVACUOUSOFF { }	| yD_ATAN { }	| yD_ATAN2 { }	| yD_ATANH { }	| yD_BITS { }	| yD_BITSTOREAL { }	| yD_BITSTOSHORTREAL { }	| yD_C { }	| yD_CAST { }	| yD_CEIL { }	| yD_CHANGED { }	| yD_CHANGED_GCLK { }	| yD_CHANGING_GCLK { }	| yD_CLOG2 { }	| yD_COS { }	| yD_COSH { }	| yD_COUNTBITS { }	| yD_COUNTONES { }	| yD_CPURE { }	| yD_DIMENSIONS { }	| yD_DISPLAY { }	| yD_DISPLAYB { }	| yD_DISPLAYH { }	| yD_DISPLAYO { }	| yD_DIST_CHI_SQUARE { }	| yD_DIST_ERLANG { }	| yD_DIST_EXPONENTIAL { }	| yD_DIST_NORMAL { }	| yD_DIST_POISSON { }	| yD_DIST_T { }	| yD_DIST_UNIFORM { }	| yD_DUMPALL { }	| yD_DUMPFILE { }	| yD_DUMPFLUSH { }	| yD_DUMPLIMIT { }	| yD_DUMPOFF { }	| yD_DUMPON { }	| yD_DUMPPORTS { }	| yD_DUMPVARS { }	| yD_ERROR { }	| yD_EXIT { }	| yD_EXP { }	| yD_FALLING_GCLK { }	| yD_FATAL { }	| yD_FCLOSE { }	| yD_FDISPLAY { }	| yD_FDISPLAYB { }	| yD_FDISPLAYH { }	| yD_FDISPLAYO { }	| yD_FELL { }	| yD_FELL_GCLK { }	| yD_FEOF { }	| yD_FERROR { }	| yD_FFLUSH { }	| yD_FGETC { }	| yD_FGETS { }	| yD_FINISH { }	| yD_FLOOR { }	| yD_FMONITOR { }	| yD_FMONITORB { }	| yD_FMONITORH { }	| yD_FMONITORO { }	| yD_FOPEN { }	| yD_FREAD { }	| yD_FREWIND { }	| yD_FSCANF { }	| yD_FSEEK { }	| yD_FSTROBE { }	| yD_FSTROBEB { }	| yD_FSTROBEH { }	| yD_FSTROBEO { }	| yD_FTELL { }	| yD_FUTURE_GCLK { }	| yD_FWRITE { }	| yD_FWRITEB { }	| yD_FWRITEH { }	| yD_FWRITEO { }	| yD_GLOBAL_CLOCK { }	| yD_HIGH { }	| yD_HYPOT { }	| yD_INCREMENT { }	| yD_INFERRED_DISABLE { }	| yD_INFO { }	| yD_ISUNBOUNDED { }	| yD_ISUNKNOWN { }	| yD_ITOR { }	| yD_LEFT { }	| yD_LN { }	| yD_LOG10 { }	| yD_LOW { }	| yD_MONITOR { }	| yD_MONITORB { }	| yD_MONITORH { }	| yD_MONITORO { }	| yD_MONITOROFF { }	| yD_MONITORON { }	| yD_ONEHOT { }	| yD_ONEHOT0 { }	| yD_PAST { }	| yD_PAST_GCLK { }	| yD_POW { }	| yD_PRINTTIMESCALE { }	| yD_RANDOM { }	| yD_READMEMB { }	| yD_READMEMH { }	| yD_REALTIME { }	| yD_REALTOBITS { }	| yD_REWIND { }	| yD_RIGHT { }	| yD_RISING_GCLK { }	| yD_ROOT { }	| yD_ROSE { }	| yD_ROSE_GCLK { }	| yD_RTOI { }	| yD_SAMPLED { }	| yD_SDF_ANNOTATE { }	| yD_SFORMAT { }	| yD_SFORMATF { }	| yD_SHORTREALTOBITS { }	| yD_SIGNED { }	| yD_SIN { }	| yD_SINH { }	| yD_SIZE { }	| yD_SQRT { }	| yD_SSCANF { }	| yD_STABLE { }	| yD_STABLE_GCLK { }	| yD_STACKTRACE { }	| yD_STEADY_GCLK { }	| yD_STIME { }	| yD_STOP { }	| yD_STROBE { }	| yD_STROBEB { }	| yD_STROBEH { }	| yD_STROBEO { }	| yD_SWRITE { }	| yD_SWRITEB { }	| yD_SWRITEH { }	| yD_SWRITEO { }	| yD_SYSTEM { }	| yD_TAN { }	| yD_TANH { }	| yD_TESTPLUSARGS { }	| yD_TIME { }	| yD_TIMEFORMAT { }	| yD_TIMEPRECISION { }	| yD_TIMEUNIT { }	| yD_TYPENAME { }	| yD_UNGETC { }	| yD_UNIT { }	| yD_UNPACKED_DIMENSIONS { }	| yD_UNSIGNED { }	| yD_URANDOM { }	| yD_URANDOM_RANGE { }	| yD_VALUEPLUSARGS { }	| yD_WARNING { }	| yD_WRITE { }	| yD_WRITEB { }	| yD_WRITEH { }	| yD_WRITEMEMB { }	| yD_WRITEMEMH { }	| yD_WRITEO { }	| yEDGE { }	| yELSE { }	| yEND { }	| yENDCASE { }	| yENDCHECKER { }	| yENDCLASS { }	| yENDCLOCKING { }	| yENDCONFIG { }	| yENDFUNCTION { }	| yENDGENERATE { }	| yENDGROUP { }	| yENDINTERFACE { }	| yENDPACKAGE { }	| yENDPRIMITIVE { }	| yENDPROGRAM { }	| yENDPROPERTY { }	| yENDSEQUENCE { }	| yENDTABLE { }	| yENDTASK { }	| yENUM { }	| yEVENT { }	| yEVENTUALLY { }	| yEXPECT { }	| yEXPORT { }	| yEXTENDS { }	| yEXTERN { }	| yFINAL { }	| yFIRST_MATCH { }	| yFOR { }	| yFORCE { }	| yFOREACH { }	| yFOREVER { }	| yFORK { }	| yFORKJOIN { }	| yFUNCTION { }	| yGENERATE { }	| yGENVAR { }	| yGLOBAL__CLOCKING { }	| yGLOBAL__ETC { }	| yGLOBAL__LEX { }	| yHIGHZ0 { }	| yHIGHZ1 { }	| yIF { }	| yIFF { }	| yIGNORE_BINS { }	| yILLEGAL_BINS { }	| yIMPLEMENTS { }	| yIMPLIES { }	| yIMPORT { }	| yINCDIR { }	| yINCLUDE { }	| yINITIAL { }	| yINOUT { }	| yINPUT { }	| yINSIDE { }	| yINSTANCE { }	| yINT { }	| yINTEGER { }	| yINTERCONNECT { }	| yINTERFACE { }	| yINTERSECT { }	| yJOIN { }	| yJOIN_ANY { }	| yJOIN_NONE { }	| yLET { }	| yLIBLIST { }	| yLIBRARY { }	| yLOCALPARAM { }	| yLOCAL__COLONCOLON { }	| yLOCAL__ETC { }	| yLOCAL__LEX { }	| yLOGIC { }	| yLONGINT { }	| yMATCHES { }	| yMODPORT { }	| yMODULE { }	| yNAND { }	| yNEGEDGE { }	| yNETTYPE { }	| yNEW__ETC { }	| yNEW__LEX { }	| yNEW__PAREN { }	| yNEXTTIME { }	| yNMOS { }	| yNOR { }	| yNOT { }	| yNOTIF0 { }	| yNOTIF1 { }	| yNULL { }	| yOR { }	| yOUTPUT { }	| yPACKAGE { }	| yPACKED { }	| yPARAMETER { }	| yPMOS { }	| yPOSEDGE { }	| yPRIMITIVE { }	| yPRIORITY { }	| yPROGRAM { }	| yPROPERTY { }	| yPROTECTED { }	| yPULL0 { }	| yPULL1 { }	| yPULLDOWN { }	| yPULLUP { }	| yPURE { }	| yP_ANDAND { }	| yP_ANDANDAND { }	| yP_ANDEQ { }	| yP_ASTGT { }	| yP_ATAT { }	| yP_BRAEQ { }	| yP_BRAMINUSGT { }	| yP_BRAPLUSKET { }	| yP_BRASTAR { }	| yP_CASEEQUAL { }	| yP_CASENOTEQUAL { }	| yP_COLONCOLON { }	| yP_COLONDIV { }	| yP_COLONEQ { }	| yP_COLON__BEGIN { }	| yP_COLON__FORK { }	| yP_DIVEQ { }	| yP_DOTSTAR { }	| yP_EQGT { }	| yP_EQUAL { }	| yP_EQ__NEW { }	| yP_GTE { }	| yP_LTE { }	| yP_LTE__IGNORE { }	| yP_LTMINUSGT { }	| yP_MINUSCOLON { }	| yP_MINUSEQ { }	| yP_MINUSGT { }	| yP_MINUSGTGT { }	| yP_MINUSMINUS { }	| yP_MODEQ { }	| yP_NAND { }	| yP_NOR { }	| yP_NOTEQUAL { }	| yP_OREQ { }	| yP_OREQGT { }	| yP_ORMINUSGT { }	| yP_OROR { }	| yP_PAR__IGNORE { }	| yP_PAR__STRENGTH { }	| yP_PLUSCOLON { }	| yP_PLUSEQ { }	| yP_PLUSPCTMINUS { }	| yP_PLUSPLUS { }	| yP_PLUSSLASHMINUS { }	| yP_POUNDEQPD { }	| yP_POUNDMINUSPD { }	| yP_POUNDPOUND { }	| yP_POW { }	| yP_SLEFT { }	| yP_SLEFTEQ { }	| yP_SRIGHT { }	| yP_SRIGHTEQ { }	| yP_SSRIGHT { }	| yP_SSRIGHTEQ { }	| yP_TICK { }	| yP_TICKBRA { }	| yP_TIMESEQ { }	| yP_WILDEQUAL { }	| yP_WILDNOTEQUAL { }	| yP_XNOR { }	| yP_XOREQ { }	| yRAND { }	| yRANDC { }	| yRANDCASE { }	| yRANDOMIZE { }	| yRANDSEQUENCE { }	| yRCMOS { }	| yREAL { }	| yREALTIME { }	| yREF { }	| yREG { }	| yREJECT_ON { }	| yRELEASE { }	| yREPEAT { }	| yRESTRICT { }	| yRETURN { }	| yRNMOS { }	| yRPMOS { }	| yRTRAN { }	| yRTRANIF0 { }	| yRTRANIF1 { }	| ySCALARED { }	| ySEQUENCE { }	| ySHORTINT { }	| ySHORTREAL { }	| ySIGNED { }	| ySOFT { }	| ySOLVE { }	| ySPECIFY { }	| ySTATIC__CONSTRAINT { }	| ySTATIC__ETC { }	| ySTATIC__LEX { }	| ySTRING { }	| ySTRONG { }	| ySTRONG0 { }	| ySTRONG1 { }	| ySTRUCT { }	| ySUPER { }	| ySUPPLY0 { }	| ySUPPLY1 { }	| ySYNC_ACCEPT_ON { }	| ySYNC_REJECT_ON { }	| yS_ALWAYS { }	| yS_EVENTUALLY { }	| yS_NEXTTIME { }	| yS_UNTIL { }	| yS_UNTIL_WITH { }	| yTABLE { }	| yTAGGED { }	| yTASK { }	| yTHIS { }	| yTHROUGHOUT { }	| yTIME { }	| yTIMEPRECISION { }	| yTIMEUNIT { }	| yTRAN { }	| yTRANIF0 { }	| yTRANIF1 { }	| yTRI { }	| yTRI0 { }	| yTRI1 { }	| yTRIAND { }	| yTRIOR { }	| yTRIREG { }	| yTRUE { }	| yTYPEDEF { }	| yTYPE__EQ { }	| yTYPE__ETC { }	| yTYPE__LEX { }	| yUNION { }	| yUNIQUE { }	| yUNIQUE0 { }	| yUNSIGNED { }	| yUNTIL { }	| yUNTIL_WITH { }	| yUNTYPED { }	| yUSE { }	| yVAR { }	| yVECTORED { }	| yVIRTUAL__CLASS { }	| yVIRTUAL__ETC { }	| yVIRTUAL__INTERFACE { }	| yVIRTUAL__LEX { }	| yVIRTUAL__anyID { }	| yVLT_CLOCKER { }	| yVLT_CLOCK_ENABLE { }	| yVLT_COVERAGE_BLOCK_OFF { }	| yVLT_COVERAGE_OFF { }	| yVLT_COVERAGE_ON { }	| yVLT_D_BLOCK { }	| yVLT_D_CONTENTS { }	| yVLT_D_COST { }	| yVLT_D_FILE { }	| yVLT_D_FUNCTION { }	| yVLT_D_HIER_DPI { }	| yVLT_D_LEVELS { }	| yVLT_D_LINES { }	| yVLT_D_MATCH { }	| yVLT_D_MODEL { }	| yVLT_D_MODULE { }	| yVLT_D_MTASK { }	| yVLT_D_PARAM { }	| yVLT_D_PORT { }	| yVLT_D_RULE { }	| yVLT_D_SCOPE { }	| yVLT_D_TASK { }	| yVLT_D_VAR { }	| yVLT_D_WORKERS { }	| yVLT_FORCEABLE { }	| yVLT_FULL_CASE { }	| yVLT_HIER_BLOCK { }	| yVLT_HIER_PARAMS { }	| yVLT_HIER_WORKERS { }	| yVLT_INLINE { }	| yVLT_ISOLATE_ASSIGNMENTS { }	| yVLT_LINT_OFF { }	| yVLT_LINT_ON { }	| yVLT_NO_CLOCKER { }	| yVLT_NO_INLINE { }	| yVLT_PARALLEL_CASE { }	| yVLT_PROFILE_DATA { }	| yVLT_PUBLIC { }	| yVLT_PUBLIC_FLAT { }	| yVLT_PUBLIC_FLAT_RD { }	| yVLT_PUBLIC_FLAT_RW { }	| yVLT_PUBLIC_MODULE { }	| yVLT_SC_BIGUINT { }	| yVLT_SC_BV { }	| yVLT_SFORMAT { }	| yVLT_SPLIT_VAR { }	| yVLT_TIMING_OFF { }	| yVLT_TIMING_ON { }	| yVLT_TRACING_OFF { }	| yVLT_TRACING_ON { }	| yVL_CLOCKER { }	| yVL_CLOCK_ENABLE { }	| yVL_COVERAGE_BLOCK_OFF { }	| yVL_FORCEABLE { }	| yVL_FULL_CASE { }	| yVL_HIER_BLOCK { }	| yVL_INLINE_MODULE { }	| yVL_ISOLATE_ASSIGNMENTS { }	| yVL_NO_CLOCKER { }	| yVL_NO_INLINE_MODULE { }	| yVL_NO_INLINE_TASK { }	| yVL_PARALLEL_CASE { }	| yVL_PUBLIC { }	| yVL_PUBLIC_FLAT { }	| yVL_PUBLIC_FLAT_ON { }	| yVL_PUBLIC_FLAT_RD { }	| yVL_PUBLIC_FLAT_RD_ON { }	| yVL_PUBLIC_FLAT_RW { }	| yVL_PUBLIC_FLAT_RW_ON { }	| yVL_PUBLIC_FLAT_RW_ON_SNS { }	| yVL_PUBLIC_MODULE { }	| yVL_PUBLIC_OFF { }	| yVL_PUBLIC_ON { }	| yVL_SC_BIGUINT { }	| yVL_SC_BV { }	| yVL_SFORMAT { }	| yVL_SPLIT_VAR { }	| yVL_TAG { }	| yVL_UNROLL_DISABLE { }	| yVL_UNROLL_FULL { }	| yVOID { }	| yWAIT { }	| yWAIT_ORDER { }	| yWAND { }	| yWEAK { }	| yWEAK0 { }	| yWEAK1 { }	| yWHILE { }	| yWILDCARD { }	| yWIRE { }	| yWITHIN { }	| yWITH__BRA { }	| yWITH__CUR { }	| yWITH__ETC { }	| yWITH__LEX { }	| yWITH__PAREN { }	| yWITH__PAREN_CUR { }	| yWOR { }	| yWREAL { }	| yXNOR { }	| yXOR { }	| yaD_PLI { }	| yaEDGEDESC { }	| yaFLOATNUM { }	| yaID__CC { }	| yaID__ETC { }	| yaID__LEX { }	| yaID__PATHPULSE { }	| yaID__aINST { }	| yaID__aTYPE { }	| yaINTNUM { }	| yaSCCTOR { }	| yaSCDTOR { }	| yaSCHDR { }	| yaSCHDRP { }	| yaSCIMP { }	| yaSCIMPH { }	| yaSCINT { }	| yaSTRING { }	| yaSTRING__IGNORE { }	| yaTABLE_FIELD { }	| yaTABLE_LINEEND { }	| yaTABLE_LRSEP { }	| yaTIMENUM { }	| yaTIMINGSPEC { }	| yaT_NOUNCONNECTED { }	| yaT_RESETALL { }	| yaT_UNCONNECTED_PULL0 { }	| yaT_UNCONNECTED_PULL1 { }	| ygenSTRENGTH { }
        |       error                                   { }  // LCOV_EXCL_LINE
        ;

//************************************************
// IDs

id:
                yaID__ETC                               { $$ = $1; $<fl>$ = $<fl>1; }
        |       yaID__PATHPULSE                         { $$ = $1; $<fl>$ = $<fl>1; }
        |       idRandomize                             { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idAny:  // Any kind of identifier
                yaID__ETC                               { $$ = $1; $<fl>$ = $<fl>1; }
        |       yaID__PATHPULSE                         { $$ = $1; $<fl>$ = $<fl>1; }
        |       yaID__aINST                             { $$ = $1; $<fl>$ = $<fl>1; }
        |       yaID__aTYPE                             { $$ = $1; $<fl>$ = $<fl>1; }
        |       idRandomize                             { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idNotPathpulse:  // Id excluding specparam PATHPULSE$, IEEE: part of specparam_assignment
                yaID__ETC                               { $$ = $1; $<fl>$ = $<fl>1; }
        |       idRandomize                             { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idPathpulse:  // Id for specparam PATHPULSE$, IEEE: part of pulse_control_specparam
                yaID__PATHPULSE                         { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idAnyAsParseRef:  // Any kind of identifier as a ParseRef
                idAny
                        { $$ = new AstParseRef{$<fl>1, *$1}; }
        ;


idInst:                   // IEEE: instance_identifier or similar with another id then '('
        //                      // See V3ParseImp::tokenPipeScanIdInst
        //                      //   [^': '@' '.'] yaID/*module_id*/ [ '#' '('...')' ] yaID/*name_of_instance*/ [ '['...']' ] '(' ...
        //                      //   [^':' @' '.'] yaID/*module_id*/ [ '#' id|etc ] yaID/*name_of_instance*/ [ '['...']' ] '(' ...
                yaID__aINST                             { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idType:                   // IEEE: class_identifier or other type identifier
        //                      // Used where reference is needed
                yaID__aTYPE                             { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idInstType:               // type_identifier for functions which have a following id then '('
                yaID__aINST                             { $$ = $1; $<fl>$ = $<fl>1; }
        |       yaID__aTYPE                             { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idCC:                     // IEEE: class/package then ::
                                // lexer matches this:  yaID_LEX [ '#' '(' ... ')' ] yP_COLONCOLON
                yaID__CC                                { $$ = $1; $<fl>$ = $<fl>1; }
        ;

idRandomize:              // Keyword as an identifier
                yRANDOMIZE                              { static string s = "randomize"; $$ = &s; $<fl>$ = $<fl>1; }
        ;

idSVKwd:                  // Warn about non-forward compatible Verilog 2001 code
        //                      // yBIT, yBYTE won't work here as causes conflicts
                yDO
                        { static string s = "do"   ; $$ = &s; ERRSVKWD($1, *$$); $<fl>$ = $<fl>1; }
        |       yFINAL
                        { static string s = "final"; $$ = &s; ERRSVKWD($1, *$$); $<fl>$ = $<fl>1; }
        ;

variable_lvalue:     // IEEE: variable_lvalue or net_lvalue
        //                      // Note many variable_lvalue's must use exprOkLvalue when arbitrary expressions may also exist
                idClassSel                              { $$ = $1; }
        |       '{' variable_lvalueConcList '}'         { $$ = $2; }
        //                      // IEEE: [ assignment_pattern_expression_type ] assignment_pattern_variable_lvalue
        //                      // We allow more assignment_pattern_expression_types then strictly required
        //UNSUP data_type  yP_TICKBRA variable_lvalueList '}'   { UNSUP }
        //UNSUP idClassSel yP_TICKBRA variable_lvalueList '}'   { UNSUP }
        //UNSUP /**/       yP_TICKBRA variable_lvalueList '}'   { UNSUP }
        |       streaming_concatenation                 { $$ = $1; }
        ;

variable_lvalueConcList:  // IEEE: part of variable_lvalue: '{' variable_lvalue { ',' variable_lvalue } '}'
                variable_lvalue                                 { $$ = $1; }
        |       variable_lvalueConcList ',' variable_lvalue     { $$ = new AstConcat{$2, $1, $3}; }
        ;

//UNSUPvariable_lvalueList<nodeExprp>:  // IEEE: part of variable_lvalue: variable_lvalue { ',' variable_lvalue }
//UNSUP         variable_lvalue                         { $$ = $1; }
//UNSUP |       variable_lvalueList ',' variable_lvalue { $$ = addNextNull($1, $3); }
//UNSUP ;

idClass:             // Misc Ref to dotted, and/or arrayed, and/or bit-ranged variable
                idDotted                                { $$ = $1; }
        //                      // IEEE: [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
        |       yTHIS '.' idDotted
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, "this"}, $3}; }
        |       ySUPER '.' idDotted
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, "super"}, $3}; }
        |       yTHIS '.' ySUPER '.' idDotted
                        { $$ = new AstDot{$4, false, new AstParseRef{$<fl>3, "super"}, $5}; }
        //                      // Expanded: package_scope idDottedSel
        |       packageClassScope idDotted              { $$ = new AstDot{$<fl>2, true, $1, $2}; }
        ;

idClassSel:          // Misc Ref to dotted, and/or arrayed, and/or bit-ranged variable
                idDottedSel                             { $$ = $1; }
        //                      // IEEE: [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
        |       yTHIS '.' idDottedSel
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, "this"}, $3}; }
        |       ySUPER '.' idDottedSel
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, "super"}, $3}; }
        |       yTHIS '.' ySUPER '.' idDottedSel
                        { $$ = new AstDot{$4, false, new AstParseRef{$<fl>3, "super"}, $5}; }
        //                      // Expanded: package_scope idDottedSel
        |       packageClassScope idDottedSel           { $$ = new AstDot{$<fl>2, true, $1, $2}; }
        ;

idClassSelForeach:
                idDottedForeach                         { $$ = $1; }
        //                      // IEEE: [ implicit_class_handle . | package_scope ] hierarchical_variable_identifier select
        |       yTHIS '.' idDottedForeach
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, "this"}, $3}; }
        |       ySUPER '.' idDottedForeach
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, "super"}, $3}; }
        |       yTHIS '.' ySUPER '.' idDottedForeach
                        { $$ = new AstDot{$4, false, new AstParseRef{$<fl>3, "super"}, $5}; }
        //                      // Expanded: package_scope idForeach
        |       packageClassScope idDottedForeach       { $$ = new AstDot{$<fl>2, true, $1, $2}; }
        ;


// Dotted identifier for typedef - must have at least one '.'
// First component is plain id or id with array index, subsequent components can have arrays
idDottedOrArrayed:
                id '.' idArrayed
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, *$1, nullptr, nullptr}, $3}; }
        |       idDottedOrArrayed '.' idArrayed
                        { $$ = new AstDot{$2, false, $1, $3}; }
        ;

idDotted:
                yD_ROOT '.' idDottedMore
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, "$root"}, $3}; }
        |       idDottedMore                            { $$ = $1; }
        ;

idDottedSel:
                yD_ROOT '.' idDottedSelMore
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, "$root"}, $3}; }
        |       idDottedSelMore                         { $$ = $1; }
        ;

idDottedForeach:
                yD_ROOT '.' idDottedMoreForeach
                        { $$ = new AstDot{$2, false, new AstParseRef{$<fl>1, "$root"}, $3}; }
        |       idDottedMoreForeach                     { $$ = $1; }
        ;

idDottedMore:
                varRefBase                              { $$ = $1; }
        |       idDottedMore '.' varRefBase             { $$ = new AstDot{$2, false, $1, $3}; }
        ;

idDottedSelMore:
                idArrayed                               { $$ = $1; }
        |       idDottedSelMore '.' idArrayed           { $$ = new AstDot{$2, false, $1, $3}; }
        ;

idDottedMoreForeach:
                idArrayedForeach                        { $$ = $1; }
        |       idDottedMoreForeach '.' idArrayedForeach        { $$ = new AstDot{$2, false, $1, $3}; }
        ;

// Single component of dotted path, maybe [#].
// Due to lookahead constraints, we can't know if [:] or [+:] are valid (last dotted part),
// we'll assume so and cleanup later.
// id below includes:
//       enum_identifier
idArrayed:               // IEEE: id + select
                id
                        { $$ = new AstParseRef{$<fl>1, *$1, nullptr, nullptr}; }
        //                      // IEEE: id + part_select_range/constant_part_select_range
        |       idArrayed '[' expr ']'                          { $$ = new AstSelBit{$2, $1, $3}; }  // Or AstArraySel, don't know yet.
        |       idArrayed '[' constExpr ':' constExpr ']'       { $$ = new AstSelExtract{$2, $1, $3, $5}; }
        //                      // IEEE: id + indexed_range/constant_indexed_range
        |       idArrayed '[' expr yP_PLUSCOLON  constExpr ']'  { $$ = new AstSelPlus{$2, $1, $3, $5}; }
        |       idArrayed '[' expr yP_MINUSCOLON constExpr ']'  { $$ = new AstSelMinus{$2, $1, $3, $5}; }
        ;

idArrayedForeach:    // IEEE: id + select (under foreach expression)
                id
                        { $$ = new AstParseRef{$<fl>1, *$1, nullptr, nullptr}; }
        //                      // IEEE: id + part_select_range/constant_part_select_range
        |       idArrayed '[' expr ']'                          { $$ = new AstSelBit{$2, $1, $3}; }  // Or AstArraySel, don't know yet.
        |       idArrayed '[' constExpr ':' constExpr ']'       { $$ = new AstSelExtract{$2, $1, $3, $5}; }
        //                      // IEEE: id + indexed_range/constant_indexed_range
        |       idArrayed '[' expr yP_PLUSCOLON  constExpr ']'  { $$ = new AstSelPlus{$2, $1, $3, $5}; }
        |       idArrayed '[' expr yP_MINUSCOLON constExpr ']'  { $$ = new AstSelMinus{$2, $1, $3, $5}; }
        //                      // IEEE: loop_variables (under foreach expression)
        //                      // To avoid conflicts we allow expr as first element, must post-check
        |       idArrayed '[' ']'
                        { $$ = new AstSelLoopVars{$2, $1, new AstEmpty{$3}}; }
        |       idArrayed '[' expr ',' loop_variables ']'
                        { $$ = new AstSelLoopVars{$2, $1, addNextNull(static_cast<AstNode*>($3), $5)}; }
        |       idArrayed '[' ',' loop_variables ']'
                        { $$ = new AstSelLoopVars{$2, $1, addNextNull(static_cast<AstNode*>(new AstEmpty{$3}), $4)}; }
        ;

// VarRef without any dots or vectorizaion
varRefBase:
                id                                      { $$ = new AstParseRef{$<fl>1, *$1}; }
        ;

// ParseRef
parseRefBase:
                id
                        { $$ = new AstParseRef{$<fl>1, *$1, nullptr, nullptr}; }
        ;

// yaSTRING shouldn't be used directly, instead via an abstraction below
str:                      // yaSTRING but with \{escapes} need decoded
                yaSTRING                                { $$ = PARSEP->newString(GRAMMARP->unquoteString($<fl>1, *$1)); }
        ;

strAsInt:
                yaSTRING
                        { // Numeric context, so IEEE 1800-2017 11.10.3 "" is a "\000"
                          $$ = new AstConst{$<fl>1, AstConst::VerilogStringLiteral{}, GRAMMARP->unquoteString($<fl>1, *$1)}; }
        ;

strAsIntIgnore:          // strAsInt, but never matches for when expr shouldn't parse strings
                yaSTRING__IGNORE                        { $$ = nullptr; yyerror("Impossible token"); }
        ;

startLabelE:
                /* empty */                             { $$ = nullptr; $<fl>$ = nullptr; }
        |       ':' idAny                               { $$ = $2; $<fl>$ = $<fl>2; }
        ;

endLabelE:
                /* empty */                             { $$ = nullptr; $<fl>$ = nullptr; }
        |       ':' idAny                               { $$ = $2; $<fl>$ = $<fl>2; }
        |       ':' yNEW__ETC                           { static string n = "new"; $$ = &n; $<fl>$ = $<fl>2; }
        ;

//************************************************
// Clocking

clocking_declaration:            // IEEE: clocking_declaration
                yCLOCKING idAny clocking_event ';' clocking_itemListE yENDCLOCKING endLabelE
                        { $$ = new AstClocking{$<fl>2, *$2, $3, $5, false, false}; }
        |       yDEFAULT yCLOCKING clocking_event ';' clocking_itemListE yENDCLOCKING endLabelE
                        { $$ = new AstClocking{$<fl>2, "", $3, $5, true, false}; }
        |       yDEFAULT yCLOCKING idAny clocking_event ';' clocking_itemListE yENDCLOCKING endLabelE
                        { $$ = new AstClocking{$<fl>3, *$3, $4, $6, true, false}; }
        |       yGLOBAL__CLOCKING yCLOCKING clocking_event ';' clocking_itemListE yENDCLOCKING endLabelE
                        { $$ = new AstClocking{$<fl>2, "", $3, $5, false, true}; }
        |       yGLOBAL__CLOCKING yCLOCKING idAny clocking_event ';' clocking_itemListE yENDCLOCKING endLabelE
                        { $$ = new AstClocking{$<fl>3, *$3, $4, $6, false, true}; }
        ;

clocking_eventE:      // IEEE: optional clocking_event
                /* empty */                             { $$ = nullptr; }
        |       clocking_event                          { $$ = $1; }
        ;

clocking_event:       // IEEE: clocking_event
        //                      // IEEE: '@' ps_identifier
        //                      // IEEE: '@' hierarchical_identifier
        //UNSUP: '@' idClassSel/*ps_identifier*/
                '@' id
                        { $$ = new AstSenItem{$<fl>2, VEdgeType::ET_CHANGED,
                                              new AstParseRef{$<fl>2, *$2, nullptr, nullptr}}; }
        |       '@' '(' event_expression ')'            { $$ = $3; }
        ;

clocking_itemListE:
                /* empty */                             { $$ = nullptr; }
        |       clocking_itemList                       { $$ = $1; }
        ;

clocking_itemList:  // IEEE: [ clocking_item ]
                clocking_item                           { $$ = $1; }
        |       clocking_itemList clocking_item         { if ($1) $$ = addNextNull($1, $2); }
        ;

clocking_item:   // IEEE: clocking_item
                yDEFAULT yINPUT clocking_skew ';'       { $$ = new AstClockingItem{$<fl>1, VDirection::INPUT, $3, nullptr}; }
        |       yDEFAULT yOUTPUT clocking_skew ';'      { $$ = new AstClockingItem{$<fl>1, VDirection::OUTPUT, $3, nullptr}; }
        |       yDEFAULT yINPUT clocking_skew yOUTPUT clocking_skew ';'
                        { $$ = new AstClockingItem{$<fl>1, VDirection::INPUT, $3, nullptr};
                          $$->addNext(new AstClockingItem{$<fl>4, VDirection::OUTPUT, $5, nullptr}); }
        |       yINPUT clocking_skewE list_of_clocking_decl_assign ';'
                        { $$ = GRAMMARP->makeClockingItemList($<fl>1, VDirection::INPUT, $2, $3); }
        |       yOUTPUT clocking_skewE list_of_clocking_decl_assign ';'
                        { $$ = GRAMMARP->makeClockingItemList($<fl>1, VDirection::OUTPUT, $2, $3); }
        |       yINPUT clocking_skewE yOUTPUT clocking_skewE list_of_clocking_decl_assign ';'
                        { $$ = GRAMMARP->makeClockingItemList($<fl>1, VDirection::INPUT, $2, $5->cloneTree(true));
                          $$->addNext(GRAMMARP->makeClockingItemList($<fl>3, VDirection::OUTPUT, $4, $5)); }
        |       yINOUT list_of_clocking_decl_assign ';'
                        { $$ = GRAMMARP->makeClockingItemList($<fl>1, VDirection::INPUT, nullptr, $2->cloneTree(true));
                          $$->addNext(GRAMMARP->makeClockingItemList($<fl>1, VDirection::OUTPUT, nullptr, $2)); }
        |       assertion_item_declaration
                        { $$ = $1;
                          for (AstNode* nodep = $1; nodep; nodep = nodep->nextp()) {
                              if (!VN_IS(nodep, Sequence)) {
                                  $$ = nullptr;
                                  BBUNSUP(nodep, "Unsupported: assertion items in clocking blocks");
                                  DEL($1);
                                  break;
                              }
                          }
                        }
        ;

list_of_clocking_decl_assign:  // IEEE: list_of_clocking_decl_assign
                clocking_decl_assign                    { $$ = $1; }
        |       list_of_clocking_decl_assign ',' clocking_decl_assign
                        { $$ = addNextNull($1, $3); }
        ;

clocking_decl_assign:    // IEEE: clocking_decl_assign
                idAnyAsParseRef/*new-signal_identifier*/ exprEqE
                        { AstParseRef* const refp = $1;
                          $$ = refp;
                          if ($2) $$ = new AstAssign{$<fl>2, refp, $2}; }
        ;

clocking_skewE:          // IEEE: [clocking_skew]
                /* empty */                             { $$ = nullptr; }
        |       clocking_skew                           { $$ = $1; }
        ;

clocking_skew:           // IEEE: clocking_skew
                delay_control                           { $$ = $1->lhsp()->unlinkFrBack(); $1->deleteTree(); }
        |      yPOSEDGE delay_controlE                  { $$ = nullptr;
                                                          BBUNSUP($1, "Unsupported: clocking event edge override"); DEL($2); }
        |      yNEGEDGE delay_controlE                  { $$ = nullptr;
                                                          BBUNSUP($1, "Unsupported: clocking event edge override"); DEL($2); }
        |      yEDGE delay_controlE                     { $$ = nullptr;
                                                          BBUNSUP($1, "Unsupported: clocking event edge override"); DEL($2); }
        ;

cycle_delay:  // IEEE: cycle_delay
               yP_POUNDPOUND yaINTNUM
                        { $$ = new AstDelay{$<fl>1, new AstConst{$<fl>2, *$2}, true}; }
        |      yP_POUNDPOUND idAnyAsParseRef
                        { $$ = new AstDelay{$<fl>1, $2, true}; }
        |      yP_POUNDPOUND '(' expr ')'
                        { $$ = new AstDelay{$<fl>1, $3, true}; }
        ;

//************************************************
// Asserts

assertion_item_declaration:  // ==IEEE: assertion_item_declaration
                property_declaration                    { $$ = $1; }
        |       sequence_declaration                    { $$ = $1; }
        |       let_declaration                         { $$ = $1; }
        ;

assertion_item:          // ==IEEE: assertion_item
                concurrent_assertion_item               { $$ = $1; }
        |       deferred_immediate_assertion_item
                        { $$ = $1 ? new AstAlways{$1->fileline(), VAlwaysKwd::ALWAYS_COMB, nullptr, $1} : nullptr; }
        ;

deferred_immediate_assertion_item:       // ==IEEE: deferred_immediate_assertion_item
                deferred_immediate_assertion_statement  { $$ = $1; }
        |       id/*block_identifier*/ ':' deferred_immediate_assertion_statement
                        { $$ = new AstBegin{$<fl>1, *$1, $3, true}; }
        ;

procedural_assertion_statement:  // ==IEEE: procedural_assertion_statement
                concurrent_assertion_statement          { $$ = $1; }
        |       immediate_assertion_statement           { $$ = $1; }
        //                      // IEEE: checker_instantiation
        //                      // Unlike modules, checkers are the only "id id (...)" form in statements.
        //UNSUP checker_instantiation                   { $$ = $1; }
        ;

immediate_assertion_statement:   // ==IEEE: immediate_assertion_statement
                simple_immediate_assertion_statement    { $$ = $1; }
        |       deferred_immediate_assertion_statement  { $$ = $1; }
        ;

simple_immediate_assertion_statement:    // ==IEEE: simple_immediate_assertion_statement
        //                      // action_block expanded here, for compatibility with AstAssert
                assertOrAssume '(' expr ')' stmt %prec prLOWER_THAN_ELSE
                        { $$ = new AstAssert{$<fl>1, $3, $5, nullptr, VAssertType::SIMPLE_IMMEDIATE, $1}; }
        |       assertOrAssume '(' expr ')'           yELSE stmt
                        { $$ = new AstAssert{$<fl>1, $3, nullptr, $6, VAssertType::SIMPLE_IMMEDIATE, $1}; }
        |       assertOrAssume '(' expr ')' stmt yELSE stmt
                        { $$ = new AstAssert{$<fl>1, $3, $5, $7, VAssertType::SIMPLE_IMMEDIATE, $1}; }
        //                      // IEEE: simple_immediate_cover_statement
        |       yCOVER '(' expr ')' stmt                { $$ = new AstCover{$1, $3, $5, VAssertType::SIMPLE_IMMEDIATE}; }
        ;

assertOrAssume:
                yASSERT                                 { $$ = VAssertDirectiveType::ASSERT; }
        |       yASSUME                                 { $$ = VAssertDirectiveType::ASSUME; }
        ;

final_zero:                     // IEEE: part of deferred_immediate_assertion_statement
                '#' yaINTNUM
                        { if ($2->isNeqZero()) { $<fl>2->v3error("Deferred assertions must use '#0' (IEEE 1800-2023 16.4)"); }
                          $$ = VAssertType::OBSERVED_DEFERRED_IMMEDIATE; }
        //                      // 1800-2012:
        |       yFINAL                                                  { $$ = VAssertType::FINAL_DEFERRED_IMMEDIATE; }
        ;

deferred_immediate_assertion_statement:  // ==IEEE: deferred_immediate_assertion_statement
        //                      // IEEE: deferred_immediate_assert_statement
                assertOrAssume final_zero '(' expr ')' stmt %prec prLOWER_THAN_ELSE
                        { $$ = new AstAssert{$<fl>1, $4, $6, nullptr, $2, $1}; }
        |       assertOrAssume final_zero '(' expr ')'           yELSE stmt
                        { $$ = new AstAssert{$<fl>1, $4, nullptr, $7, $2, $1}; }
        |       assertOrAssume final_zero '(' expr ')' stmt yELSE stmt
                        { $$ = new AstAssert{$<fl>1, $4, $6, $8, $2, $1}; }
        //                      // IEEE: deferred_immediate_cover_statement
        |       yCOVER final_zero '(' expr ')' stmt     { $$ = new AstCover{$1, $4, $6, $2}; }
        ;

concurrent_assertion_item:       // IEEE: concurrent_assertion_item
                concurrent_assertion_statement          { $$ = $1; }
        |       id/*block_identifier*/ ':' concurrent_assertion_statement
                        { $$ = new AstBegin{$<fl>1, *$1, $3, true}; }
        //                      // IEEE: checker_instantiation
        //                      // identical to module_instantiation; see etcInst
        ;

concurrent_assertion_statement:  // ==IEEE: concurrent_assertion_statement
        //                      // IEEE: assert_property_statement
        //                      // IEEE: assume_property_statement
        //                      // action_block expanded here
                assertOrAssume yPROPERTY '(' property_spec ')' stmt %prec prLOWER_THAN_ELSE
                        { $$ = new AstAssert{$<fl>1, $4, $6, nullptr, VAssertType::CONCURRENT, $1}; }
        |       assertOrAssume yPROPERTY '(' property_spec ')' stmt yELSE stmt
                        { $$ = new AstAssert{$<fl>1, $4, $6, $8, VAssertType::CONCURRENT, $1}; }
        |       assertOrAssume yPROPERTY '(' property_spec ')' yELSE stmt
                        { $$ = new AstAssert{$<fl>1, $4, nullptr, $7, VAssertType::CONCURRENT, $1}; }
        //                      // IEEE: cover_property_statement
        |       yCOVER yPROPERTY '(' property_spec ')' stmt
                        { $$ = new AstCover{$1, $4, $6, VAssertType::CONCURRENT}; }
        //                      // IEEE: cover_sequence_statement
        |       yCOVER ySEQUENCE '(' sexpr ')' stmt
                        { $$ = nullptr; BBCOVERIGN($2, "Ignoring unsupported: cover sequence"); DEL($4, $6); }
        //                      // IEEE: yCOVER ySEQUENCE '(' clocking_event sexpr ')' stmt
        //                      // sexpr already includes "clocking_event sexpr"
        |       yCOVER ySEQUENCE '(' clocking_event yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' sexpr ')' stmt
                        { $$ = nullptr; BBCOVERIGN($2, "Ignoring unsupported: cover sequence"); DEL($4, $8, $10, $12);}
        |       yCOVER ySEQUENCE '(' yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' sexpr ')' stmt
                        { $$ = nullptr; BBCOVERIGN($2, "Ignoring unsupported: cover sequence"); DEL($7, $9, $11); }
        //                      // IEEE: restrict_property_statement
        |       yRESTRICT yPROPERTY '(' property_spec ')' ';'
                        { $$ = new AstRestrict{$1, $4}; }
        ;

property_declaration:  // ==IEEE: property_declaration
                property_declarationFront property_port_listE ';' property_declarationBody
                        yENDPROPERTY endLabelE
                        { $$ = $1;
                          $$->addStmtsp($2);
                          $$->addStmtsp($4);
                          GRAMMARP->endLabel($<fl>6, $$, $6);
                          GRAMMARP->m_insideProperty = false;
                          GRAMMARP->m_typedPropertyPort = false; }
        ;

property_declarationFront:  // IEEE: part of property_declaration
                yPROPERTY idAny/*property_identifier*/
                        { $$ = new AstProperty{$<fl>2, *$2, nullptr};
                          GRAMMARP->m_insideProperty = true; }
        ;

property_port_listE:  // IEEE: [ ( [ property_port_list ] ) ]
                /* empty */                             { $$ = nullptr; }
        |       '(' ')'                                 { $$ = nullptr; }
        |       '(' property_port_list ')'              { $$ = $2; }
        ;

property_port_list:  // ==IEEE: property_port_list
                property_port_item                              { $$ = $1; }
        |       property_port_list ',' property_port_item       { $$ = addNextNull($1, $3); }
        ;

property_port_item:  // IEEE: property_port_item/sequence_port_item
        //                      // Merged in sequence_port_item
        //                      // IEEE: property_lvar_port_direction ::= yINPUT
        //                      // prop IEEE: [ yLOCAL [ yINPUT ] ] property_formal_type
        //                      //           id {variable_dimension} [ '=' property_actual_arg ]
        //                      // seq IEEE: [ yLOCAL [ sequence_lvar_port_direction ] ] sequence_formal_type
        //                      //           id {variable_dimension} [ '=' sequence_actual_arg ]
                property_port_itemFront property_port_itemAssignment  { $$ = $2; }
        ;

property_port_itemFront:  // IEEE: part of property_port_item/sequence_port_item
                property_port_itemDirE property_formal_typeNoDt
                        { VARDTYPE($2); }
        //                      // data_type_or_implicit
        |       property_port_itemDirE data_type
                        { VARDTYPE($2); GRAMMARP->m_typedPropertyPort = true; }
        |       property_port_itemDirE yVAR data_type
                        { VARDTYPE($3); GRAMMARP->m_typedPropertyPort = true; }
        |       property_port_itemDirE yVAR implicit_typeE
                        { VARDTYPE($3); }
        |       property_port_itemDirE implicit_typeE
                        { VARDTYPE($2); }
        ;

property_port_itemAssignment:  // IEEE: part of property_port_item/sequence_port_item
                id variable_dimensionListE
                        { $$ = VARDONEA($<fl>1, *$1, $2, nullptr); }
        |       id variable_dimensionListE '=' property_actual_arg
                        { $$ = VARDONEA($<fl>1, *$1, $2, $4);
                          BBUNSUP($3, "Unsupported: property variable default value"); }
        ;

property_port_itemDirE:
                /* empty */
                        { VARIO(INPUT); }
        |       yLOCAL__ETC
                        { VARIO(INPUT);
                          BBUNSUP($1, "Unsupported: property port 'local'"); }
        |       yLOCAL__ETC yINPUT
                        { VARIO(INPUT);
                          BBUNSUP($1, "Unsupported: property port 'local'"); }
        ;

property_declarationBody:  // IEEE: part of property_declaration
                assertion_variable_declarationList property_spec
                        { $$ = nullptr; BBUNSUP($1->fileline(), "Unsupported: property variable declaration"); DEL($1, $2); }
        |       assertion_variable_declarationList property_spec ';'
                        { $$ = nullptr; BBUNSUP($1->fileline(), "Unsupported: property variable declaration"); DEL($1, $2); }
        //                      // IEEE-2012: Incorrectly has yCOVER ySEQUENCE then property_spec here.
        //                      // Fixed in IEEE 1800-2017
        |       property_spec                           { $$ = $1; }
        |       property_spec ';'                       { $$ = $1; }
        ;

assertion_variable_declarationList:  // IEEE: part of assertion_variable_declaration
                assertion_variable_declaration          { $$ = $1; }
        |       assertion_variable_declarationList assertion_variable_declaration
                        { $$ = addNextNull($1, $2); }
        ;

sequence_declaration:  // ==IEEE: sequence_declaration
                sequence_declarationFront sequence_port_listE ';' sequence_declarationBody
        /*cont*/    yENDSEQUENCE endLabelE
                        { $$ = $1;
                          $$->addStmtsp($2);
                          $$->addStmtsp($4);
                          GRAMMARP->endLabel($<fl>6, $$, $6);
                          // No error on UVM special case with no reference; see t_sequence_unused.v
                          if (! (!$$->stmtsp() || (VN_IS($$->stmtsp(), Const) && !$$->stmtsp()->nextp())))
                              $$->v3warn(E_UNSUPPORTED, "Unsupported: sequence");
                        }
        ;

sequence_declarationFront:  // IEEE: part of sequence_declaration
                ySEQUENCE idAny/*new_sequence*/
                        { $$ = new AstSequence{$<fl>2, *$2, nullptr}; }
        ;

sequence_port_listE:  // IEEE: [ ( [ sequence_port_list ] ) ]
        //                      // IEEE: sequence_lvar_port_direction ::= yINPUT | yINOUT | yOUTPUT
        //                      // IEEE: [ yLOCAL [ sequence_lvar_port_direction ] ] sequence_formal_type
        //                      //           id {variable_dimension} [ '=' sequence_actual_arg ]
        //                      // All this is almost identically the same as a property.
        //                      // Difference is only yINOUT/yOUTPUT (which might be added to 1800-2012)
        //                      // and yPROPERTY.  So save some work.
                property_port_listE                     { $$ = $1; }
        ;

property_formal_typeNoDt:  // IEEE: property_formal_type (w/o implicit)
                sequence_formal_typeNoDt                { $$ = $1; }
        |       yPROPERTY
                        { $$ = nullptr; GRAMMARP->m_typedPropertyPort = false;
                          BBUNSUP($1, "Unsupported: property argument data type"); }
        ;

sequence_formal_typeNoDt:  // ==IEEE: sequence_formal_type (w/o data_type_or_implicit)
                        // IEEE: data_type_or_implicit
                        // implicit expanded where used
                ySEQUENCE
                        { $$ = nullptr; GRAMMARP->m_typedPropertyPort = false;
                          BBUNSUP($1, "Unsupported: sequence argument data type"); }
                        // IEEE-2009: yEVENT
                        // already part of data_type.  Removed in 1800-2012.
        |       yUNTYPED
                        { $$ = nullptr; GRAMMARP->m_typedPropertyPort = false; }
        ;

sequence_declarationBody:  // IEEE: part of sequence_declaration
        //                      // 1800-2012 makes ';' optional
                assertion_variable_declarationList sexpr        { $$ = addNextNull($1, $2); }
        |       assertion_variable_declarationList sexpr ';'    { $$ = addNextNull($1, $2); }
        |       sexpr                                   { $$ = $1; }
        |       sexpr ';'                               { $$ = $1; }
        ;

property_spec:               // IEEE: property_spec
        //UNSUP: This rule has been super-specialized to what is supported now
        //UNSUP remove below
                '@' '(' senitem ')' yDISABLE yIFF '(' expr ')' pexpr
                        { $$ = new AstPropSpec{$1, $3, $8, $10}; }
        |       '@' '(' senitem ')' pexpr
                        { $$ = new AstPropSpec{$1, $3, nullptr, $5}; }
        |       '@' senitemVar pexpr
                        { $$ = new AstPropSpec{$1, $2, nullptr, $3}; }
        //                      // Disable applied after the event occurs,
        //                      // so no existing AST can represent this
        |       yDISABLE yIFF '(' expr ')' '@' '(' senitemEdge ')' pexpr
                        { $$ = new AstPropSpec{$1, $8, nullptr, new AstLogOr{$1, $4, $10}};
                          BBUNSUP($<fl>1, "Unsupported: property '(disable iff (...) @ (...)'\n"
                                  + $<fl>1->warnMore()
                                  + "... Suggest use property '(@(...) disable iff (...))'"); }
        //UNSUP remove above
        |       yDISABLE yIFF '(' expr ')' pexpr        { $$ = new AstPropSpec{$4->fileline(), nullptr, $4, $6}; }
        |       pexpr                                   { $$ = new AstPropSpec{$1->fileline(), nullptr, nullptr, $1}; }
        ;

//UNSUPproperty_statement_spec<nodep>:  // ==IEEE: property_statement_spec
//UNSUP //                      // IEEE: [ clocking_event ] [ yDISABLE yIFF '(' expression_or_dist ')' ] property_statement
//UNSUP         property_statement                      { $$ = $1; }
//UNSUP |       yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' property_statement     { }
//UNSUP //                      // IEEE: clocking_event property_statement
//UNSUP //                      // IEEE: clocking_event yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' property_statement
//UNSUP //                      // Both overlap pexpr:"clocking_event pexpr"  the difference is
//UNSUP //                      // property_statement:property_statementCaseIf so replicate it
//UNSUP |       clocking_event property_statementCaseIf { }
//UNSUP |       clocking_event yDISABLE yIFF '(' expr/*expression_or_dist*/ ')' property_statementCaseIf        { }
//UNSUP ;

//UNSUPproperty_statement<nodep>:  // ==IEEE: property_statement
//UNSUP //                      // Doesn't make sense to have "pexpr ;" in pexpr rule itself, so we split out case/if
//UNSUP         pexpr ';'                               { $$ = $1; }
//UNSUP //                      // Note this term replicated in property_statement_spec
//UNSUP //                      // If committee adds terms, they may need to be there too.
//UNSUP |       property_statementCaseIf                { $$ = $1; }
//UNSUP ;

property_statementCaseIf:  // IEEE: property_statement - minus pexpr
                yCASE '(' expr/*expression_or_dist*/ ')' property_case_itemList yENDCASE
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: property case expression");
                          DEL($3, $5); }
        |       yCASE '(' expr/*expression_or_dist*/ ')' yENDCASE
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: property case expression");
                          DEL($3); }
        |       yIF '(' expr/*expression_or_dist*/ ')' pexpr  %prec prLOWER_THAN_ELSE
                        { $$ = $5; BBUNSUP($<fl>1, "Unsupported: property case expression"); DEL($3); }
        |       yIF '(' expr/*expression_or_dist*/ ')' pexpr yELSE pexpr
                        { $$ = $5; BBUNSUP($<fl>1, "Unsupported: property case expression"); DEL($3, $7); }
        ;

property_case_itemList:  // IEEE: {property_case_item}
                property_case_item                      { $$ = $1; }
        |       property_case_itemList ',' property_case_item   { $$ = addNextNull($1, $3); }
        ;

property_case_item:  // ==IEEE: property_case_item
        //                      // IEEE: expression_or_dist { ',' expression_or_dist } ':' property_statement
        //                      // IEEE 1800-2012 changed from property_statement to property_expr
        //                      // IEEE 1800-2017 changed to require the semicolon
                caseCondList ':' pexpr                  { $$ = new AstCaseItem{$2, $1, $3}; }
        |       caseCondList ':' pexpr ';'              { $$ = new AstCaseItem{$2, $1, $3}; }
        |       yDEFAULT pexpr                          { $$ = new AstCaseItem{$1, nullptr, $2}; }
        |       yDEFAULT ':' pexpr ';'                  { $$ = new AstCaseItem{$1, nullptr, $3}; }
        ;

//UNSUPpev_expr<nodep>:  // IEEE: property_actual_arg | expr
//UNSUP //                      //       which expands to pexpr | event_expression
//UNSUP //                      // Used in port and function calls, when we can't know yet if something
//UNSUP //                      // is a function/sequence/property or instance/checker pin.
//UNSUP //
//UNSUP //                      // '(' pev_expr ')'
//UNSUP //                      // Already in pexpr
//UNSUP //                      // IEEE: event_expression ',' event_expression
//UNSUP //                      // ','s are legal in event_expressions, but parens required to avoid conflict with port-sep-,
//UNSUP //                      // IEEE: event_expression yOR event_expression
//UNSUP //                      // Already in pexpr - needs removal there
//UNSUP //                      // IEEE: event_expression yIFF expr
//UNSUP //                      // Already in pexpr - needs removal there
//UNSUP //
//UNSUP         senitemEdge                             { $$ = $1; }
//UNSUP //
//UNSUP //============= pexpr rules copied for pev_expr
//UNSUP |       BISONPRE_COPY_ONCE(pexpr,{s/p/pev_/g; })     // {copied}
//UNSUP //
//UNSUP //============= sexpr rules copied for pev_expr
//UNSUP |       BISONPRE_COPY_ONCE(sexpr,{s/s/pev_/g; })     // {copied}
//UNSUP //
//UNSUP //============= expr rules copied for pev_expr
//UNSUP |       BISONPRE_COPY_ONCE(expr,{s//pev_/g; s//pev_/g; s/'.'/yP_PAR__IGNORE /g; })    // {copied}
//UNSUP ;

pexpr:  // IEEE: property_expr  (The name pexpr is important as regexps just add an "p" to expr.)
        //
        //                      // IEEE: sequence_expr
        //                      // Expanded below
        //
        //                      // IEEE: '(' pexpr ')'
        //                      // Expanded below
        //
                yNOT pexpr
                        { $$ = new AstLogNot{$1, $2}; }
        |       ySTRONG '(' sexpr ')'
                        { $$ = $3; BBUNSUP($2, "Unsupported: strong (in property expression)"); }
        |       yWEAK '(' sexpr ')'
                        { $$ = $3; BBUNSUP($2, "Unsupported: weak (in property expression)"); }
        //                      // IEEE: pexpr yOR pexpr
        //                      // IEEE: pexpr yAND pexpr
        //                      // Under sexpr and/or sexpr
        //
        //                      // IEEE: "sequence_expr yP_ORMINUSGT pexpr"
        //                      // Instead we use pexpr to prevent conflicts
        |       pexpr yP_ORMINUSGT pexpr             { $$ = new AstImplication{$2, $1, $3, true}; }
        |       pexpr yP_OREQGT pexpr                { $$ = new AstImplication{$2, $1, $3, false}; }
        //
        //                      // IEEE-2009: property_statement
        //                      // IEEE-2012: yIF and yCASE
        |       property_statementCaseIf                { $$ = $1; }
        //
        |       pexpr/*sexpr*/ yP_POUNDMINUSPD pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: #-# (in property expression)"); DEL($3); }
        |       pexpr/*sexpr*/ yP_POUNDEQPD pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: #=# (in property expression)"); DEL($3); }
        |       yNEXTTIME pexpr
                        { $$ = $2; BBUNSUP($1, "Unsupported: nexttime (in property expression)"); }
        |       yS_NEXTTIME pexpr
                        { $$ = $2; BBUNSUP($1, "Unsupported: s_nexttime (in property expression)"); }
        |       yNEXTTIME '[' constExpr ']' pexpr %prec yNEXTTIME
                        { $$ = $5; BBUNSUP($1, "Unsupported: nexttime[] (in property expression)"); DEL($3); }
        |       yS_NEXTTIME '[' constExpr ']' pexpr %prec yS_NEXTTIME
                        { $$ = $5; BBUNSUP($1, "Unsupported: s_nexttime[] (in property expression)"); DEL($3); }
        |       yALWAYS pexpr
                        { $$ = $2; BBUNSUP($1, "Unsupported: always (in property expression)"); }
        |       yALWAYS anyrange pexpr  %prec yALWAYS
                        { $$ = $3; BBUNSUP($1, "Unsupported: always[] (in property expression)"); DEL($2); }
        |       yS_ALWAYS anyrange pexpr  %prec yS_ALWAYS
                        { $$ = $3; BBUNSUP($1, "Unsupported: s_always (in property expression)"); DEL($2); }
        |       yS_EVENTUALLY pexpr
                        { $$ = $2; BBUNSUP($1, "Unsupported: s_eventually (in property expression)"); }
        |       yS_EVENTUALLY anyrange pexpr  %prec yS_EVENTUALLY
                        { $$ = $3; BBUNSUP($1, "Unsupported: s_eventually[] (in property expression)"); DEL($2); }
        |       yEVENTUALLY anyrange pexpr  %prec yS_EVENTUALLY
                        { $$ = $3; BBUNSUP($1, "Unsupported: eventually[] (in property expression)"); DEL($2); }
        |       pexpr yUNTIL pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: until (in property expression)"); DEL($3); }
        |       pexpr yS_UNTIL pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: s_until (in property expression)"); DEL($3); }
        |       pexpr yUNTIL_WITH pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: until_with (in property expression)"); DEL($3); }
        |       pexpr yS_UNTIL_WITH pexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: s_until_with (in property expression)"); DEL($3); }
        |       pexpr yIMPLIES pexpr
                        { $$ = new AstLogOr{$2, new AstLogNot{$2, $1}, $3}; }
        //                      // yIFF also used by event_expression
        |       pexpr yIFF pexpr
                        { $$ = new AstLogEq{$2, $1, $3}; }
        |       yACCEPT_ON '(' expr/*expression_or_dist*/ ')' pexpr  %prec yACCEPT_ON
                        { $$ = $5; BBUNSUP($2, "Unsupported: accept_on (in property expression)"); DEL($3); }
        |       yREJECT_ON '(' expr/*expression_or_dist*/ ')' pexpr  %prec yREJECT_ON
                        { $$ = $5; BBUNSUP($2, "Unsupported: reject_on (in property expression)"); DEL($3); }
        |       ySYNC_ACCEPT_ON '(' expr/*expression_or_dist*/ ')' pexpr %prec ySYNC_ACCEPT_ON
                        { $$ = $5; BBUNSUP($2, "Unsupported: sync_accept_on (in property expression)"); DEL($3); }
        |       ySYNC_REJECT_ON '(' expr/*expression_or_dist*/ ')' pexpr %prec ySYNC_REJECT_ON
                        { $$ = $5; BBUNSUP($2, "Unsupported: sync_reject_on (in property expression)"); DEL($3); }
        //
        //                      // IEEE: "property_instance"
        //                      // Looks just like a function/method call
        //
        //                      // Note "clocking_event pexpr" overlaps
        //                      // property_statement_spec: clocking_event property_statement
        //
        //                      // Include property_specDisable to match property_spec rule
        //UNSUP clocking_event yDISABLE yIFF '(' expr ')' pexpr %prec prSEQ_CLOCKING    { }
        //
        //============= sexpr rules copied for property_expr
        |                        cycle_delay_range pexpr  %prec yP_POUNDPOUND                         { $$ = new AstSExpr{$<fl>1, $1, $2}; }         |       pexpr cycle_delay_range sexpr %prec prPOUNDPOUND_MULTI                         { $$ = new AstSExpr{$<fl>2, $1, $2, $3}; }         |       pexpr/*sexpression_or_dist*/ boolean_abbrev                         { $$ = $1; BBUNSUP($2->fileline(), "Unsupported: boolean abbrev (in sequence expression)"); DEL($2); }         |       '(' pexpr ')'                        { $$ = $2; }         |       '(' pexpr ',' sequence_match_itemList ')'                         { $$ = $2; BBUNSUP($3, "Unsupported: sequence match items"); DEL($4); }         |       pexpr yAND pexpr                         { $$ = new AstLogAnd{$2, $1, $3};                           BBUNSUP($2, "Unsupported: and (in sequence expression)"); }         |       pexpr yOR pexpr                         { $$ = new AstLogOr{$2, $1, $3};                           BBUNSUP($2, "Unsupported: or (in sequence expression)"); }         |       pexpr yINTERSECT sexpr                         { $$ = $1; BBUNSUP($2, "Unsupported: intersect (in sequence expression)"); DEL($3); }         |       yFIRST_MATCH '(' sexpr ')'                         { $$ = $3; BBUNSUP($1, "Unsupported: first_match (in sequence expression)"); }         |       yFIRST_MATCH '(' sexpr ',' sequence_match_itemList ')'                         { $$ = $3; BBUNSUP($1, "Unsupported: first_match (in sequence expression)"); DEL($5); }         |       pexpr/*sexpression_or_dist*/ yTHROUGHOUT sexpr                         { $$ = $1; BBUNSUP($2, "Unsupported: throughout (in sequence expression)"); DEL($3); }         |       pexpr yWITHIN sexpr                         { $$ = $1; BBUNSUP($2, "Unsupported: within (in sequence expression)"); DEL($3); }                  // {copied}
        //
        //============= expr rules copied for property_expr
        |                        '+' expr     %prec prUNARYARITH      { $$ = $2; }         |       '-' expr     %prec prUNARYARITH      { $$ = new AstNegate{$1, $2}; }         |       '!' expr     %prec prNEGATION        { $$ = new AstLogNot{$1, $2}; }         |       '&' expr     %prec prREDUCTION       { $$ = new AstRedAnd{$1, $2}; }         |       '~' expr     %prec prNEGATION        { $$ = new AstNot{$1, $2}; }         |       '|' expr     %prec prREDUCTION       { $$ = new AstRedOr{$1, $2}; }         |       '^' expr     %prec prREDUCTION       { $$ = new AstRedXor{$1, $2}; }         |       yP_NAND expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedAnd{$1, $2}}; }         |       yP_NOR  expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedOr{$1, $2}}; }         |       yP_XNOR expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedXor{$1, $2}}; }         |       pinc_or_dec_expression                { $<fl>$ = $<fl>1; $$ = $1; }         |       '(' pexprScope '='          expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, $4},                                                $2->cloneTreePure(true)};                           ASSIGNEQEXPR($<fl>3); }         |       '(' pexprScope yP_PLUSEQ    expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAdd{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' pexprScope yP_MINUSEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstSub{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' pexprScope yP_TIMESEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstMul{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' pexprScope yP_DIVEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstDiv{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' pexprScope yP_MODEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstModDiv{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' pexprScope yP_ANDEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAnd{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' pexprScope yP_OREQ      expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstOr{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' pexprScope yP_XOREQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstXor{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' pexprScope yP_SLEFTEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftL{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' pexprScope yP_SRIGHTEQ  expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftR{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' pexprScope yP_SSRIGHTEQ expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftRS{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       pexpr '+' expr                     { $$ = new AstAdd{$2, $1, $3}; }         |       pexpr '-' expr                     { $$ = new AstSub{$2, $1, $3}; }         |       pexpr '*' expr                     { $$ = new AstMul{$2, $1, $3}; }         |       pexpr '/' expr                     { $$ = new AstDiv{$2, $1, $3}; }         |       pexpr '%' expr                     { $$ = new AstModDiv{$2, $1, $3}; }         |       pexpr yP_EQUAL expr                { $$ = new AstEq{$2, $1, $3}; }         |       pexpr yP_NOTEQUAL expr             { $$ = new AstNeq{$2, $1, $3}; }         |       pexpr yP_CASEEQUAL expr            { $$ = new AstEqCase{$2, $1, $3}; }         |       pexpr yP_CASENOTEQUAL expr         { $$ = new AstNeqCase{$2, $1, $3}; }         |       pexpr yP_WILDEQUAL expr            { $$ = new AstEqWild{$2, $1, $3}; }         |       pexpr yP_WILDNOTEQUAL expr         { $$ = new AstNeqWild{$2, $1, $3}; }         |       pexpr yP_ANDAND expr               { $$ = new AstLogAnd{$2, $1, $3}; }         |       pexpr yP_OROR expr                 { $$ = new AstLogOr{$2, $1, $3}; }         |       pexpr yP_POW expr                  { $$ = new AstPow{$2, $1, $3}; }         |       pexpr '<' expr                     { $$ = new AstLt{$2, $1, $3}; }         |       pexpr '>' expr                     { $$ = new AstGt{$2, $1, $3}; }         |       pexpr yP_GTE expr                  { $$ = new AstGte{$2, $1, $3}; }         |       pexpr '&' expr                     { $$ = new AstAnd{$2, $1, $3}; }         |       pexpr '|' expr                     { $$ = new AstOr{$2, $1, $3}; }         |       pexpr '^' expr                     { $$ = new AstXor{$2, $1, $3}; }         |       pexpr yP_XNOR expr                 { $$ = new AstNot{$2, new AstXor{$2, $1, $3}}; }         |       pexpr yP_NOR expr                  { $$ = new AstNot{$2, new AstOr{$2, $1, $3}}; }         |       pexpr yP_NAND expr                 { $$ = new AstNot{$2, new AstAnd{$2, $1, $3}}; }         |       pexpr yP_SLEFT expr                { $$ = new AstShiftL{$2, $1, $3}; }         |       pexpr yP_SRIGHT expr               { $$ = new AstShiftR{$2, $1, $3}; }         |       pexpr yP_SSRIGHT expr              { $$ = new AstShiftRS{$2, $1, $3}; }         |       pexpr yP_LTMINUSGT expr            { $$ = new AstLogEq{$2, $1, $3}; }         |       type_referenceEq yP_CASEEQUAL type_referenceBoth     { $$ = new AstEqT{$2, $1, $3}; }         |       type_referenceEq yP_CASENOTEQUAL type_referenceBoth  { $$ = new AstNeqT{$2, $1, $3}; }         |       type_referenceEq yP_EQUAL type_referenceBoth         { $$ = new AstEqT{$2, $1, $3}; }         |       type_referenceEq yP_NOTEQUAL type_referenceBoth      { $$ = new AstNeqT{$2, $1, $3}; }         |       pexpr yP_MINUSGT expr              { $$ = new AstLogIf{$2, $1, $3}; }         |       pexpr yP_LTE expr       { $$ = new AstLte{$2, $1, $3}; }         |       pexpr '?' expr ':' expr         { $$ = new AstCond{$2, $1, $3, $5}; }         |       pexpr yINSIDE '{' range_list '}'      { $$ = new AstInside{$2, $1, $4}; }         |       yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }         |       yaFLOATNUM                              { $$ = new AstConst{$<fl>1, AstConst::RealDouble{}, $1}; }         |       timeNumAdjusted                         { $$ = $1; }         |       strAsInt                 { $$ = $1; }         |       '{' '}'                                 { $$ = new AstEmptyQueue{$1}; }         |       '{' constExpr '{' cateList '}' '}'                         { $$ = new AstReplicate{$3, $4, $2}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr ']'                         { $$ = new AstSelBit{$7, new AstReplicate{$3, $4, $2}, $8}; }         |       '{' constExpr '{' cateList '}' '}' '[' constExpr ':' constExpr ']'                         { $$ = new AstSelExtract{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr yP_PLUSCOLON constExpr ']'                         { $$ = new AstSelPlus{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr yP_MINUSCOLON constExpr ']'                         { $$ = new AstSelMinus{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       function_subroutine_callNoMethod                         { $$ = $1; }         |       function_subroutine_callNoMethod part_select_rangeList                         { $$ = GRAMMARP->scrubSel($1, $2); }         |       pexpr '.' function_subroutine_callNoMethod                         { $$ = new AstDot{$2, false, $1, $3}; }         |       pexpr '.' function_subroutine_callNoMethod part_select_rangeList                         { $$ = GRAMMARP->scrubSel(new AstDot{$2, false, $1, $3}, $4); }         |       pexpr '.' array_methodWith                         { $$ = new AstDot{$2, false, $1, $3}; }         |       pexpr '.' array_methodWith part_select_rangeList                         { $$ = GRAMMARP->scrubSel(new AstDot{$2, false, $1, $3}, $4); }         |       yP_PAR__IGNORE  expr ')'             { $$ = $2; }         |       yP_PAR__IGNORE  expr ':' expr ':' expr ')'                         { $$ = $4; MINTYPMAXDLYUNSUP($4); DEL($2); DEL($6); }         |       '_' '(' expr ')'                        { $$ = $3; }         |       simple_typeNoRef yP_TICK '(' expr ')'                         { $$ = new AstCast{$2, $4, VFlagChildDType{}, $1}; }         |       yTYPE__ETC '(' exprOrDataType ')' yP_TICK '(' expr ')'                         { $$ = new AstCast{$1, $7, VFlagChildDType{},                                            new AstRefDType{$1, AstRefDType::FlagTypeOfExpr{}, $3}}; }         |       ySIGNED yP_TICK '(' expr ')'            { $$ = new AstSigned{$1, $4}; }         |       yUNSIGNED yP_TICK '(' expr ')'          { $$ = new AstUnsigned{$1, $4}; }         |       ySTRING yP_TICK '(' expr ')'            { $$ = new AstCvtPackString{$1, $4}; }         |       yCONST__ETC yP_TICK '(' expr ')'        { $$ = $4; }         |       pexpr yP_TICK '(' expr ')'            { $$ = new AstCastParse{$2, $4, $1}; }         |       '$'                                     { $$ = new AstUnbounded{$<fl>1}; }         |       yNULL                                   { $$ = new AstConst{$1, AstConst::Null{}}; }         |       pexprOkLvalue                         { $$ = $1; }         |       pexpr yP_ANDANDAND expr            { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: &&& expression"); }         |       pexpr yMATCHES patternNoExpr          { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: matches operator"); }         |       pexpr yMATCHES expr                { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: matches operator"); }         |       pexpr yDIST '{' dist_list '}'         { $$ = new AstDist{$2, $1, $4}; }   // {copied}
        ;

sexpr:  // ==IEEE: sequence_expr  (The name sexpr is important as regexps just add an "s" to expr.)
        //                      // ********* RULES COPIED IN sequence_exprProp
        //                      // For precedence, see IEEE 17.7.1
        //
        //                      // IEEE: "cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }"
        //                      // IEEE: "sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }"
        //                      // Both rules basically mean we can repeat sequences, so make it simpler:
                cycle_delay_range sexpr  %prec yP_POUNDPOUND
                        { $$ = new AstSExpr{$<fl>1, $1, $2}; }
        |       sexpr cycle_delay_range sexpr %prec prPOUNDPOUND_MULTI
                        { $$ = new AstSExpr{$<fl>2, $1, $2, $3}; }
        //
        //                      // IEEE: expression_or_dist [ boolean_abbrev ]
        //                      // Note expression_or_dist includes "expr"!
        //                      // sexpr/*sexpression_or_dist*/  --- Hardcoded below
        |       sexpr/*sexpression_or_dist*/ boolean_abbrev
                        { $$ = $1; BBUNSUP($2->fileline(), "Unsupported: boolean abbrev (in sequence expression)"); DEL($2); }
        //
        //                      // IEEE: "sequence_instance [ sequence_abbrev ]"
        //                      // version without sequence_abbrev looks just like normal function call
        //                      // version w/sequence_abbrev matches above;
        //                      // expression_or_dist:expr:func boolean_abbrev:sequence_abbrev
        //
        //                      // IEEE: '(' expression_or_dist {',' sequence_match_item } ')' [ boolean_abbrev ]
        //                      // IEEE: '(' sexpr {',' sequence_match_item } ')' [ sequence_abbrev ]
        //                      // As sequence_expr includes expression_or_dist, and boolean_abbrev includes sequence_abbrev:
        //                      // '(' sequence_expr {',' sequence_match_item } ')' [ boolean_abbrev ]
        //                      // "'(' sexpr ')' boolean_abbrev" matches "[sexpr:'(' expr ')'] boolean_abbrev" so we can drop it
        |       '(' sexpr ')'                        { $$ = $2; }
        |       '(' sexpr ',' sequence_match_itemList ')'
                        { $$ = $2; BBUNSUP($3, "Unsupported: sequence match items"); DEL($4); }
        //
        //                      // AND/OR are between pexprs OR sexprs
        |       sexpr yAND sexpr
                        { $$ = new AstLogAnd{$2, $1, $3};
                          BBUNSUP($2, "Unsupported: and (in sequence expression)"); }
        |       sexpr yOR sexpr
                        { $$ = new AstLogOr{$2, $1, $3};
                          BBUNSUP($2, "Unsupported: or (in sequence expression)"); }
        //                      // Intersect always has an sexpr rhs
        |       sexpr yINTERSECT sexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: intersect (in sequence expression)"); DEL($3); }
        //
        |       yFIRST_MATCH '(' sexpr ')'
                        { $$ = $3; BBUNSUP($1, "Unsupported: first_match (in sequence expression)"); }
        |       yFIRST_MATCH '(' sexpr ',' sequence_match_itemList ')'
                        { $$ = $3; BBUNSUP($1, "Unsupported: first_match (in sequence expression)"); DEL($5); }
        |       sexpr/*sexpression_or_dist*/ yTHROUGHOUT sexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: throughout (in sequence expression)"); DEL($3); }
        //                      // Below pexpr's are really sequence_expr, but avoid conflict
        //                      // IEEE: sexpr yWITHIN sexpr
        |       sexpr yWITHIN sexpr
                        { $$ = $1; BBUNSUP($2, "Unsupported: within (in sequence expression)"); DEL($3); }
        //                      // Note concurrent_assertion had duplicate rule for below
        //UNSUP clocking_event sexpr %prec prSEQ_CLOCKING    { }
        //
        //============= expr rules copied for sequence_expr
        |                        '+' expr     %prec prUNARYARITH      { $$ = $2; }         |       '-' expr     %prec prUNARYARITH      { $$ = new AstNegate{$1, $2}; }         |       '!' expr     %prec prNEGATION        { $$ = new AstLogNot{$1, $2}; }         |       '&' expr     %prec prREDUCTION       { $$ = new AstRedAnd{$1, $2}; }         |       '~' expr     %prec prNEGATION        { $$ = new AstNot{$1, $2}; }         |       '|' expr     %prec prREDUCTION       { $$ = new AstRedOr{$1, $2}; }         |       '^' expr     %prec prREDUCTION       { $$ = new AstRedXor{$1, $2}; }         |       yP_NAND expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedAnd{$1, $2}}; }         |       yP_NOR  expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedOr{$1, $2}}; }         |       yP_XNOR expr %prec prREDUCTION       { $$ = new AstLogNot{$1, new AstRedXor{$1, $2}}; }         |       sinc_or_dec_expression                { $<fl>$ = $<fl>1; $$ = $1; }         |       '(' sexprScope '='          expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, $4},                                                $2->cloneTreePure(true)};                           ASSIGNEQEXPR($<fl>3); }         |       '(' sexprScope yP_PLUSEQ    expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAdd{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' sexprScope yP_MINUSEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstSub{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' sexprScope yP_TIMESEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstMul{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' sexprScope yP_DIVEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstDiv{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' sexprScope yP_MODEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstModDiv{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' sexprScope yP_ANDEQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstAnd{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' sexprScope yP_OREQ      expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstOr{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' sexprScope yP_XOREQ     expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstXor{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' sexprScope yP_SLEFTEQ   expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftL{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' sexprScope yP_SRIGHTEQ  expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftR{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       '(' sexprScope yP_SSRIGHTEQ expr ')'                         { $$ = new AstExprStmt{$1, new AstAssign{$3, $2, new AstShiftRS{$3, $2->cloneTreePure(true), $4}},                                                $2->cloneTreePure(true)}; }         |       sexpr '+' expr                     { $$ = new AstAdd{$2, $1, $3}; }         |       sexpr '-' expr                     { $$ = new AstSub{$2, $1, $3}; }         |       sexpr '*' expr                     { $$ = new AstMul{$2, $1, $3}; }         |       sexpr '/' expr                     { $$ = new AstDiv{$2, $1, $3}; }         |       sexpr '%' expr                     { $$ = new AstModDiv{$2, $1, $3}; }         |       sexpr yP_EQUAL expr                { $$ = new AstEq{$2, $1, $3}; }         |       sexpr yP_NOTEQUAL expr             { $$ = new AstNeq{$2, $1, $3}; }         |       sexpr yP_CASEEQUAL expr            { $$ = new AstEqCase{$2, $1, $3}; }         |       sexpr yP_CASENOTEQUAL expr         { $$ = new AstNeqCase{$2, $1, $3}; }         |       sexpr yP_WILDEQUAL expr            { $$ = new AstEqWild{$2, $1, $3}; }         |       sexpr yP_WILDNOTEQUAL expr         { $$ = new AstNeqWild{$2, $1, $3}; }         |       sexpr yP_ANDAND expr               { $$ = new AstLogAnd{$2, $1, $3}; }         |       sexpr yP_OROR expr                 { $$ = new AstLogOr{$2, $1, $3}; }         |       sexpr yP_POW expr                  { $$ = new AstPow{$2, $1, $3}; }         |       sexpr '<' expr                     { $$ = new AstLt{$2, $1, $3}; }         |       sexpr '>' expr                     { $$ = new AstGt{$2, $1, $3}; }         |       sexpr yP_GTE expr                  { $$ = new AstGte{$2, $1, $3}; }         |       sexpr '&' expr                     { $$ = new AstAnd{$2, $1, $3}; }         |       sexpr '|' expr                     { $$ = new AstOr{$2, $1, $3}; }         |       sexpr '^' expr                     { $$ = new AstXor{$2, $1, $3}; }         |       sexpr yP_XNOR expr                 { $$ = new AstNot{$2, new AstXor{$2, $1, $3}}; }         |       sexpr yP_NOR expr                  { $$ = new AstNot{$2, new AstOr{$2, $1, $3}}; }         |       sexpr yP_NAND expr                 { $$ = new AstNot{$2, new AstAnd{$2, $1, $3}}; }         |       sexpr yP_SLEFT expr                { $$ = new AstShiftL{$2, $1, $3}; }         |       sexpr yP_SRIGHT expr               { $$ = new AstShiftR{$2, $1, $3}; }         |       sexpr yP_SSRIGHT expr              { $$ = new AstShiftRS{$2, $1, $3}; }         |       sexpr yP_LTMINUSGT expr            { $$ = new AstLogEq{$2, $1, $3}; }         |       type_referenceEq yP_CASEEQUAL type_referenceBoth     { $$ = new AstEqT{$2, $1, $3}; }         |       type_referenceEq yP_CASENOTEQUAL type_referenceBoth  { $$ = new AstNeqT{$2, $1, $3}; }         |       type_referenceEq yP_EQUAL type_referenceBoth         { $$ = new AstEqT{$2, $1, $3}; }         |       type_referenceEq yP_NOTEQUAL type_referenceBoth      { $$ = new AstNeqT{$2, $1, $3}; }         |       sexpr yP_MINUSGT expr              { $$ = new AstLogIf{$2, $1, $3}; }         |       sexpr yP_LTE expr       { $$ = new AstLte{$2, $1, $3}; }         |       sexpr '?' expr ':' expr         { $$ = new AstCond{$2, $1, $3, $5}; }         |       sexpr yINSIDE '{' range_list '}'      { $$ = new AstInside{$2, $1, $4}; }         |       yaINTNUM                                { $$ = new AstConst{$<fl>1, *$1}; }         |       yaFLOATNUM                              { $$ = new AstConst{$<fl>1, AstConst::RealDouble{}, $1}; }         |       timeNumAdjusted                         { $$ = $1; }         |       strAsInt                 { $$ = $1; }         |       '{' '}'                                 { $$ = new AstEmptyQueue{$1}; }         |       '{' constExpr '{' cateList '}' '}'                         { $$ = new AstReplicate{$3, $4, $2}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr ']'                         { $$ = new AstSelBit{$7, new AstReplicate{$3, $4, $2}, $8}; }         |       '{' constExpr '{' cateList '}' '}' '[' constExpr ':' constExpr ']'                         { $$ = new AstSelExtract{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr yP_PLUSCOLON constExpr ']'                         { $$ = new AstSelPlus{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       '{' constExpr '{' cateList '}' '}' '[' expr yP_MINUSCOLON constExpr ']'                         { $$ = new AstSelMinus{$7, new AstReplicate{$3, $4, $2}, $8, $10}; }         |       function_subroutine_callNoMethod                         { $$ = $1; }         |       function_subroutine_callNoMethod part_select_rangeList                         { $$ = GRAMMARP->scrubSel($1, $2); }         |       sexpr '.' function_subroutine_callNoMethod                         { $$ = new AstDot{$2, false, $1, $3}; }         |       sexpr '.' function_subroutine_callNoMethod part_select_rangeList                         { $$ = GRAMMARP->scrubSel(new AstDot{$2, false, $1, $3}, $4); }         |       sexpr '.' array_methodWith                         { $$ = new AstDot{$2, false, $1, $3}; }         |       sexpr '.' array_methodWith part_select_rangeList                         { $$ = GRAMMARP->scrubSel(new AstDot{$2, false, $1, $3}, $4); }         |       yP_PAR__IGNORE  expr ')'             { $$ = $2; }         |       yP_PAR__IGNORE  expr ':' expr ':' expr ')'                         { $$ = $4; MINTYPMAXDLYUNSUP($4); DEL($2); DEL($6); }         |       '_' '(' expr ')'                        { $$ = $3; }         |       simple_typeNoRef yP_TICK '(' expr ')'                         { $$ = new AstCast{$2, $4, VFlagChildDType{}, $1}; }         |       yTYPE__ETC '(' exprOrDataType ')' yP_TICK '(' expr ')'                         { $$ = new AstCast{$1, $7, VFlagChildDType{},                                            new AstRefDType{$1, AstRefDType::FlagTypeOfExpr{}, $3}}; }         |       ySIGNED yP_TICK '(' expr ')'            { $$ = new AstSigned{$1, $4}; }         |       yUNSIGNED yP_TICK '(' expr ')'          { $$ = new AstUnsigned{$1, $4}; }         |       ySTRING yP_TICK '(' expr ')'            { $$ = new AstCvtPackString{$1, $4}; }         |       yCONST__ETC yP_TICK '(' expr ')'        { $$ = $4; }         |       sexpr yP_TICK '(' expr ')'            { $$ = new AstCastParse{$2, $4, $1}; }         |       '$'                                     { $$ = new AstUnbounded{$<fl>1}; }         |       yNULL                                   { $$ = new AstConst{$1, AstConst::Null{}}; }         |       sexprOkLvalue                         { $$ = $1; }         |       sexpr yP_ANDANDAND expr            { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: &&& expression"); }         |       sexpr yMATCHES patternNoExpr          { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: matches operator"); }         |       sexpr yMATCHES expr                { $$ = new AstConst{$2, AstConst::BitFalse{}};                                                           BBUNSUP($<fl>2, "Unsupported: matches operator"); }         |       sexpr yDIST '{' dist_list '}'         { $$ = new AstDist{$2, $1, $4}; }   // {copied}
        ;

cycle_delay_range:  // IEEE: ==cycle_delay_range
        //                      // These three terms in 1800-2005 ONLY
                yP_POUNDPOUND intnumAsConst
                        { $$ = new AstDelay{$1, $2, true}; }
        |       yP_POUNDPOUND idAny
                        { $$ = new AstDelay{$1, new AstParseRef{$<fl>2, *$2}, true}; }
        |       yP_POUNDPOUND '(' constExpr ')'
                        { $$ = new AstDelay{$1, $3, true}; }
        //                      // In 1800-2009 ONLY:
        //                      // IEEE: yP_POUNDPOUND constant_primary
        //                      // UNSUP: This causes a big grammar ambiguity
        //                      // as ()'s mismatch between primary and the following statement
        //                      // the sv-ac committee has been asked to clarify  (Mantis 1901)
        |       yP_POUNDPOUND anyrange
                        { $$ = new AstDelay{$1, new AstConst{$1, AstConst::BitFalse{}}, true};
                          DEL($2);
                          BBUNSUP($<fl>1, "Unsupported: ## range cycle delay range expression"); }
        |       yP_POUNDPOUND yP_BRASTAR ']'
                        { $$ = new AstDelay{$1, new AstConst{$1, AstConst::BitFalse{}}, true};
                          BBUNSUP($<fl>1, "Unsupported: ## [*] cycle delay range expression"); }
        |       yP_POUNDPOUND yP_BRAPLUSKET
                        { $$ = new AstDelay{$1, new AstConst{$1, AstConst::BitFalse{}}, true};
                          BBUNSUP($<fl>1, "Unsupported: ## [+] cycle delay range expression"); }
        ;

sequence_match_itemList:  // IEEE: [sequence_match_item] part of sequence_expr
                sequence_match_item                     { $$ = $1; }
        |       sequence_match_itemList ',' sequence_match_item { $$ = addNextNull($1, $3); }
        ;

sequence_match_item:  // ==IEEE: sequence_match_item
        //                      // IEEE says: operator_assignment
        //                      // IEEE says: inc_or_dec_expression
        //                      // IEEE says: subroutine_call
        //                      // This is the same list as...
                for_step_assignment                     { $$ = $1; }
        ;

boolean_abbrev:  // ==IEEE: boolean_abbrev
        //                      // IEEE: consecutive_repetition
                yP_BRASTAR constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [*] boolean abbrev expression"); }
        |       yP_BRASTAR constExpr ':' constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [*] boolean abbrev expression"); DEL($4); }
        |       yP_BRASTAR ']'
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: [*] boolean abbrev expression"); }
        |       yP_BRAPLUSKET
                        { $$ = new AstConst{$1, AstConst::BitFalse{}};
                          BBUNSUP($<fl>1, "Unsupported: [+] boolean abbrev expression"); }
        //                      // IEEE: nonconsecutive_repetition/non_consecutive_repetition
        |       yP_BRAEQ constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [= boolean abbrev expression"); }
        |       yP_BRAEQ constExpr ':' constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [= boolean abbrev expression"); DEL($4); }
        //                      // IEEE: goto_repetition
        |       yP_BRAMINUSGT constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [-> boolean abbrev expression"); }
        |       yP_BRAMINUSGT constExpr ':' constExpr ']'
                        { $$ = $2; BBUNSUP($<fl>1, "Unsupported: [-> boolean abbrev expression"); DEL($4); }
        ;

//************************************************
// Covergroup

covergroup_declaration:  // ==IEEE: covergroup_declaration
                 yCOVERGROUP idAny cgPortListE coverage_eventE ';'
        /*cont*/    coverage_spec_or_optionListE
        /*cont*/ yENDGROUP endLabelE
                        { AstClass *cgClassp = new AstClass{$<fl>2, *$2, PARSEP->libname()};
                          cgClassp->isCovergroup(true);
                          AstFunc* const newp = new AstFunc{$<fl>1, "new", nullptr, nullptr};
                          newp->fileline()->warnOff(V3ErrorCode::NORETURN, true);
                          newp->classMethod(true);
                          newp->isConstructor(true);
                          newp->dtypep(cgClassp->dtypep());
                          newp->addStmtsp($3);
                          newp->addStmtsp($6);
                          cgClassp->addMembersp(newp);
                          GRAMMARP->createCoverGroupMethods(cgClassp, $4);

                          $$ = cgClassp;
                          GRAMMARP->endLabel($<fl>8, $$, $8);
                          BBCOVERIGN($<fl>1, "Ignoring unsupported: covergroup");
                        }
        |        yCOVERGROUP yEXTENDS idAny ';'
        /*cont*/     coverage_spec_or_optionListE
        /*cont*/ yENDGROUP endLabelE
                        { AstClass *cgClassp = new AstClass{$<fl>3, *$3, PARSEP->libname()};
                          cgClassp->isCovergroup(true);
                          AstFunc* const newp = new AstFunc{$<fl>1, "new", nullptr, nullptr};
                          newp->fileline()->warnOff(V3ErrorCode::NORETURN, true);
                          newp->classMethod(true);
                          newp->isConstructor(true);
                          newp->dtypep(cgClassp->dtypep());
                          newp->addStmtsp($5);
                          cgClassp->addMembersp(newp);
                          GRAMMARP->createCoverGroupMethods(cgClassp, nullptr);

                          $$ = cgClassp;
                          GRAMMARP->endLabel($<fl>7, $$, $7);
                          BBCOVERIGN($<fl>1, "Ignoring unsupported: covergroup");
                        }
        ;

cgPortListE:
                /*empty*/                               { $$ = nullptr; }
        |       '(' tf_port_listE ')'                   { $$ = $2; }
        ;

cgexpr:  // IEEE-2012: covergroup_expression, before that just expression
                expr                                    { $$ = $1; }
        ;

coverage_spec_or_optionListE:  // IEEE: [{coverage_spec_or_option}]
                /* empty */                             { $$ = nullptr; }
        |       coverage_spec_or_optionList             { $$ = $1; }
        ;

coverage_spec_or_optionList:  // IEEE: {coverage_spec_or_option}
                coverage_spec_or_option                 { $$ = $1; }
        |       coverage_spec_or_optionList coverage_spec_or_option     { $$ = addNextNull($1, $2); }
        ;

coverage_spec_or_option:  // ==IEEE: coverage_spec_or_option
        //                      // IEEE: coverage_spec
                cover_point                             { $$ = $1; }
        |       cover_cross                             { $$ = $1; }
        |       coverage_option ';'                     { $$ = $1; }
        |       error                                   { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

coverage_option:  // ==IEEE: coverage_option
        //                      // option/type_option aren't really keywords
                id/*yOPTION | yTYPE_OPTION*/ '.' idAny/*member_identifier*/ '=' expr
                        { if (*$1 == "option") {
                              $$ = new AstCgOptionAssign{$<fl>1, false, *$3, $5};
                          } else if (*$1 == "type_option") {
                              $$ = new AstCgOptionAssign{$<fl>1, true, *$3, $5};
                          } else {
                              $$ = nullptr;
                              $<fl>1->v3error("Syntax error; expected 'option' or 'type_option': '" << *$1 << "'");
                              DEL($5);
                          } }
        ;

cover_point:  // ==IEEE: cover_point
        //              // [ [ data_type_or_implicit ] cover_point_identifier ':' ] yCOVERPOINT
                yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBCOVERIGN($<fl>1, "Ignoring unsupported: coverpoint"); DEL($2, $3, $4); }
        //                      // IEEE-2012: class_scope before an ID
        |       id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBCOVERIGN($<fl>3, "Ignoring unsupported: coverpoint"); DEL($4, $5, $6);}
        //                      // data_type_or_implicit expansion
        |       data_type id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBCOVERIGN($<fl>4, "Ignoring unsupported: coverpoint"); DEL($1, $5, $6, $7);}
        |       yVAR data_type id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBCOVERIGN($<fl>5, "Ignoring unsupported: coverpoint"); DEL($2, $6, $7, $8); }
        |       yVAR implicit_typeE id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBCOVERIGN($<fl>5, "Ignoring unsupported: coverpoint"); DEL($2, $6, $7, $8); }
        |       signingE rangeList id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBCOVERIGN($<fl>5, "Ignoring unsupported: coverpoint"); DEL($2, $6, $7, $8); }
        |       signing id/*cover_point_id*/ ':' yCOVERPOINT expr iffE bins_or_empty
                        { $$ = nullptr; BBCOVERIGN($<fl>4, "Ignoring unsupported: coverpoint"); DEL($5, $6, $7); }
        //                      // IEEE-2012:
        |       bins_or_empty                           { $$ = $1; }
        ;

iffE:  // IEEE: part of cover_point, others
                /* empty */                             { $$ = nullptr; }
        |       yIFF '(' expr ')'
                        { $$ = nullptr; BBCOVERIGN($<fl>1, "Ignoring unsupported: cover 'iff'"); DEL($3); }
        ;

bins_or_empty:  // ==IEEE: bins_or_empty
                '{' bins_or_optionsList '}'             { $$ = $2; }
        |       '{' '}'                                 { $$ = nullptr; }
        |       ';'                                     { $$ = nullptr; }
        //
        |       '{' bins_or_optionsList error '}'       { $$ = $2; }  // LCOV_EXCL_LINE
        |       '{' error '}'                           { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

bins_or_optionsList:  // IEEE: { bins_or_options ';' }
                bins_or_options ';'                     { $$ = $1; }
        |       bins_or_optionsList bins_or_options ';' { $$ = addNextNull($1, $2); }
        //
        |       bins_or_optionsList error ';'           { $$ = $1; }  // LCOV_EXCL_LINE
        |       error ';'                               { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

bins_or_options:  // ==IEEE: bins_or_options
        //                      // Superset of IEEE - we allow []'s in more places
                coverage_option                         { $$ = $1; }
        //                      // Can't use wildcardE as results in conflicts
        |       bins_keyword idAny/*bin_identifier*/ bins_orBraE '=' '{' range_list '}' iffE
                        { $$ = nullptr; BBCOVERIGN($<fl>4, "Ignoring unsupported: cover bin specification"); DEL($3, $6, $8); }
        |       bins_keyword idAny/*bin_identifier*/ bins_orBraE '=' '{' range_list '}' yWITH__PAREN '(' cgexpr ')' iffE
                        { $$ = nullptr; BBCOVERIGN($<fl>8, "Ignoring unsupported: cover bin 'with' specification"); DEL($3, $6, $10, $12); }
        |       yWILDCARD bins_keyword idAny/*bin_identifier*/ bins_orBraE '=' '{' range_list '}' iffE
                        { $$ = nullptr; BBCOVERIGN($<fl>5, "Ignoring unsupported: cover bin 'wildcard' specification"); DEL($4, $7, $9); }
        |       yWILDCARD bins_keyword idAny/*bin_identifier*/ bins_orBraE '=' '{' range_list '}' yWITH__PAREN '(' cgexpr ')' iffE
                        { $$ = nullptr; BBCOVERIGN($<fl>9, "Ignoring unsupported: cover bin 'wildcard' 'with' specification"); DEL($4, $7, $11, $13); }
        //
        //                      // cgexpr part of trans_list
        |       bins_keyword idAny/*bin_identifier*/ bins_orBraE '=' trans_list iffE
                        { $$ = nullptr; BBCOVERIGN($<fl>4, "Ignoring unsupported: cover bin trans list"); DEL($3, $5, $6); }
        |       yWILDCARD bins_keyword idAny/*bin_identifier*/ bins_orBraE '=' trans_list iffE
                        { $$ = nullptr; BBCOVERIGN($<fl>1, "Ignoring unsupported: cover bin 'wildcard' trans list"); DEL($4, $6, $7);}
        //
        |       bins_keyword idAny/*bin_identifier*/ bins_orBraE '=' yDEFAULT iffE
                        { $$ = nullptr; BBCOVERIGN($<fl>5, "Ignoring unsupported: cover bin 'default'"); DEL($3, $6); }
        |       bins_keyword idAny/*bin_identifier*/ bins_orBraE '=' yDEFAULT ySEQUENCE iffE
                        { $$ = nullptr; BBCOVERIGN($<fl>6, "Ignoring unsupported: cover bin 'default' 'sequence'"); DEL($3, $7); }
        ;

bins_orBraE:  // IEEE: part of bins_or_options:
                /* empty */                             { $$ = nullptr; }
        |       '[' ']'                                 { $$ = nullptr; /*UNSUP*/ }
        |       '[' cgexpr ']'                          { $$ = nullptr; /*UNSUP*/ DEL($2); }
        ;

bins_keyword:  // ==IEEE: bins_keyword
                yBINS                                   { $$ = $1; /*UNSUP*/ }
        |       yILLEGAL_BINS                           { $$ = $1; /*UNSUP*/ }
        |       yIGNORE_BINS                            { $$ = $1; /*UNSUP*/ }
        ;

trans_list:  // ==IEEE: trans_list
                '(' trans_set ')'                       { $$ = $2; }
        |       trans_list ',' '(' trans_set ')'        { $$ = addNextNull($1, $4); }
        ;

trans_set:  // ==IEEE: trans_set
                trans_range_list                        { $$ = $1; }
        //                      // Note the { => } in the grammar, this is really a list
        |       trans_set yP_EQGT trans_range_list
                        { $$ = $1; BBCOVERIGN($<fl>2, "Ignoring unsupported: cover trans set '=>'"); DEL($3); }
        ;

trans_range_list:  // ==IEEE: trans_range_list
                trans_item                              { $$ = $1; }
        |       trans_item yP_BRASTAR cgexpr ']'
                        { $$ = nullptr; BBCOVERIGN($<fl>2, "Ignoring unsupported: cover '[*'"); DEL($1, $3); }
        |       trans_item yP_BRASTAR cgexpr ':' cgexpr ']'
                        { $$ = nullptr; BBCOVERIGN($<fl>2, "Ignoring unsupported: cover '[*'"); DEL($1, $3, $5); }
        |       trans_item yP_BRAMINUSGT cgexpr ']'
                        { $$ = nullptr; BBCOVERIGN($<fl>2, "Ignoring unsupported: cover '[->'"); DEL($1, $3); }
        |       trans_item yP_BRAMINUSGT cgexpr ':' cgexpr ']'
                        { $$ = nullptr; BBCOVERIGN($<fl>2, "Ignoring unsupported: cover '[->'"); DEL($1, $3, $5); }
        |       trans_item yP_BRAEQ cgexpr ']'
                        { $$ = nullptr; BBCOVERIGN($<fl>2, "Ignoring unsupported: cover '[='"); DEL($1, $3); }
        |       trans_item yP_BRAEQ cgexpr ':' cgexpr ']'
                        { $$ = nullptr; BBCOVERIGN($<fl>2, "Ignoring unsupported: cover '[='"); DEL($1, $3, $5); }
        ;

trans_item:  // ==IEEE: range_list
                covergroup_range_list                   { $$ = $1; }
        ;

covergroup_range_list:  // ==IEEE: covergroup_range_list
                covergroup_value_range                  { $$ = $1; }
        |       covergroup_range_list ',' covergroup_value_range        { $$ = addNextNull($1, $3); }
        ;


cover_cross:  // ==IEEE: cover_cross
                id/*cover_point_identifier*/ ':' yCROSS list_of_cross_items iffE cross_body
                        { $$ = nullptr; BBCOVERIGN($<fl>3, "Ignoring unsupported: cover cross"); DEL($4, $5, $6); }
        |       yCROSS list_of_cross_items iffE cross_body
                        { $$ = nullptr; BBCOVERIGN($<fl>1, "Ignoring unsupported: cover cross"); DEL($2, $3, $4); }
        ;

list_of_cross_items:  // ==IEEE: list_of_cross_items
                cross_item ',' cross_item               { $$ = addNextNull($1, $3); }
        |       cross_item ',' cross_item ',' cross_itemList
                        { $$ = addNextNull(addNextNull($1, $3), $5); }
        ;

cross_itemList:  // IEEE: part of list_of_cross_items
                cross_item                              { $$ = $1; }
        |       cross_itemList ',' cross_item           { $$ = addNextNull($1, $3); }
        ;

cross_item:  // ==IEEE: cross_item
                idDotted/*cover_point_identifier or variable_identifier*/  { $1->deleteTree(); $$ = nullptr; /*UNSUP*/ }
        ;

cross_body:  // ==IEEE: cross_body
                '{' '}'                                 { $$ = nullptr; }
        //                      // IEEE-2012: No semicolon here, mistake in spec
        |       '{' cross_body_itemList '}'             { $$ = $2; }
        |       ';'                                     { $$ = nullptr; }
        //
        |       '{' cross_body_itemList error '}'       { $$ = $2; }  // LCOV_EXCL_LINE
        |       '{' error '}'                           { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

cross_body_itemList:  // IEEE: part of cross_body
                cross_body_item                         { $$ = $1; }
        |       cross_body_itemList cross_body_item     { $$ = addNextNull($1, $2); }
        ;

cross_body_item:  // ==IEEE: cross_body_item
                function_declaration
                        { $$ = $1; BBCOVERIGN($1->fileline(), "Ignoring unsupported: coverage cross 'function' declaration"); }
        //                      // IEEE: bins_selection_or_option
        |       coverage_option ';'                     { $$ = $1; }
        //                      // IEEE: bins_selection
        |       bins_keyword idAny/*new-bin_identifier*/ '=' select_expression iffE ';'
                        { $$ = nullptr; BBCOVERIGN($1, "Ignoring unsupported: coverage cross bin"); DEL($4, $5); }
        |       error ';'                               { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

select_expression:  // ==IEEE: select_expression
                select_expression_r
                        { $$ = $1; }
        |       select_expression yP_ANDAND select_expression
                        { $$ = nullptr; BBCOVERIGN($2, "Ignoring unsupported: coverage select expression '&&'"); DEL($1, $3); }
        |       select_expression yP_OROR   select_expression
                        { $$ = nullptr; BBCOVERIGN($2, "Ignoring unsupported: coverage select expression '||'"); DEL($1, $3); }
        ;

// This non-terminal exists to disambiguate select_expression and make "with" bind tighter
select_expression_r:
        //                      // IEEE: select_condition expanded here
                yBINSOF '(' bins_expression ')'
                        { $$ = nullptr; BBCOVERIGN($1, "Ignoring unsupported: coverage select expression 'binsof'"); DEL($3); }
        |       '!' yBINSOF '(' bins_expression ')'
                        { $$ = nullptr; BBCOVERIGN($1, "Ignoring unsupported: coverage select expression 'binsof'"); DEL($4); }
        |       yBINSOF '(' bins_expression ')' yINTERSECT '{' covergroup_range_list '}'
                        { $$ = nullptr; BBCOVERIGN($5, "Ignoring unsupported: coverage select expression 'intersect'"); DEL($3, $7); }
        |       '!' yBINSOF '(' bins_expression ')' yINTERSECT '{' covergroup_range_list '}'    { }
                        { $$ = nullptr; BBCOVERIGN($5, "Ignoring unsupported: coverage select expression 'intersect'"); DEL($4, $8); }
        |       yWITH__PAREN '(' cgexpr ')'
                        { $$ = nullptr; BBCOVERIGN($1, "Ignoring unsupported: coverage select expression with"); DEL($3); }
        |       '!' yWITH__PAREN '(' cgexpr ')'
                        { $$ = nullptr; BBCOVERIGN($1, "Ignoring unsupported: coverage select expression with"); DEL($4); }
        |       select_expression_r yWITH__PAREN '(' cgexpr ')'
                        { $$ = nullptr; BBCOVERIGN($2, "Ignoring unsupported: coverage select expression with"); DEL($1, $4); }
        //                      // IEEE-2012: Need clarification as to precedence
        //UNSUP yWITH__PAREN '(' cgexpr ')' yMATCHES cgexpr    { }
        //                      // IEEE-2012: Need clarification as to precedence
        //UNSUP '!' yWITH__PAREN '(' cgexpr ')' yMATCHES cgexpr { }
        //
        |       '(' select_expression ')'                       { $$ = $2; }
        //                      // IEEE-2012: cross_identifier
        //                      // Part of covergroup_expression - generic identifier
        //                      // IEEE-2012: Need clarification as to precedence
        //UNSUP  cgexpr  { $$ = nullptr; BBCOVERIGN($1, "Ignoring unsupported: coverage select expression"); }
        //
        //                      // IEEE: cross_set_expression [ yMATCHES integer_covergroup_expression ]
        //                      // covergroup_expression [ yMATCHES ( integer_covergroup_expression | '$' ) ]
        //                      // Need precedence fix
        //UNSUP  cgexpr yMATCHES cgexpr    {..}
        //UNSUP                 // Below are all removed
        |       idAny '(' list_of_argumentsE ')'
                        { $$ = nullptr; BBCOVERIGN($<fl>1, "Ignoring unsupported: coverage select function call"); DEL($3); }
        //UNSUP                 // Above are all removed, replace with:
        ;

bins_expression:  // ==IEEE: bins_expression
        //                      // "cover_point_identifier" and "variable_identifier" look identical
        // IEEE specifies:
        // bins_expression ::=
        //    variable_identifier
        //    | cover_point_identifier [ . bin_identifier ]
        // Verilator supports hierarchical reference in a place of variable identifier.
        // This is an extension based on other simulators.
               idDotted
                        { $$ = nullptr; /*UNSUP*/ DEL($1); }
        ;

coverage_eventE:  // IEEE: [ coverage_event ]
                /* empty */                             { $$ = nullptr; }
        |       clocking_event
                        { $$ = nullptr; BBCOVERIGN($<fl>1, "Ignoring unsupported: coverage clocking event"); DEL($1); }
        |       yWITH__ETC yFUNCTION idAny/*"sample"*/ '(' tf_port_listE ')'
                        { if (*$3 != "sample") {
                            $<fl>3->v3error("Coverage sampling function must be named 'sample'");
                            $$ = nullptr;
                            DEL($5);
                          } else {
                            $$ = $5;
                          }
                        }
        |       yP_ATAT '(' block_event_expression ')'
                        { $$ = nullptr; BBCOVERIGN($<fl>1, "Ignoring unsupported: coverage '@@' events"); DEL($3); }
        ;

block_event_expression:  // ==IEEE: block_event_expression
                block_event_expressionTerm              { $$ = nullptr; /*UNSUP @@*/ DEL($1); }
        |       block_event_expression yOR block_event_expressionTerm   { $$ = nullptr; /*UNSUP @@*/ DEL($1, $3);  }
        ;

block_event_expressionTerm:  // IEEE: part of block_event_expression
                yBEGIN hierarchical_btf_identifier      { $$ = nullptr; /*UNSUP @@*/ DEL($2); }
        |       yEND   hierarchical_btf_identifier      { $$ = nullptr; /*UNSUP @@*/ DEL($2); }
        ;

hierarchical_btf_identifier:  // ==IEEE: hierarchical_btf_identifier
        //                      // hierarchical_tf_identifier + hierarchical_block_identifier
        //                      // method_identifier
                packageClassScopeE idAny                { $$ = nullptr; /*UNSUP*/ DEL($1); }
        ;

//**********************************************************************
// Randsequence

randsequence_statement:  // ==IEEE: randsequence_statement
                yRANDSEQUENCE '(' ')' rs_productionList yENDSEQUENCE
                        { $$ = new AstRandSequence{$1, "", $4};
                          v3Global.useRandSequence(true); }
        |       yRANDSEQUENCE '(' idAny/*rs_production_identifier*/ ')' rs_productionList yENDSEQUENCE
                        { $$ = new AstRandSequence{$1, *$3, $5};
                          v3Global.useRandSequence(true); }
        ;

rs_productionList:  // IEEE: rs_production+
                rs_production                           { $$ = $1; }
        |       rs_productionList rs_production         { $$ = addNextNull($1, $2); }
        ;

rs_production:  // ==IEEE: rs_production
                rs_productionFront ':' rs_ruleList ';'
                        { $$ = $1; $1->addRulesp($3); }
        ;

rs_productionFront:  // IEEE: part of rs_production
                rs_funcId/*rs_production_identifier*/   { $$ = $1; }
        |       rs_funcId '(' tf_port_listE ')'         { $$ = $1; $$->addPortsp($3); }
        ;

rs_funcId:  // IEEE: part of rs_production
                /**/ rs_fId
                        { $$ = $1; }  // Note is void as default, not logic as default like functions
        |       signingE rangeList rs_fId
                        { $$ = $3;
                          $$->fvarp(new AstVar{$<fl>1, VVarType::PORT, $3->name(), VFlagChildDType{},
                                               GRAMMARP->addRange(new AstBasicDType{$<fl>3, LOGIC_IMPLICIT, $1}, $2, true)}); }
        |       signing rs_fId
                        { $$ = $2;
                          $$->fvarp(new AstVar{$<fl>1, VVarType::PORT, $2->name(), VFlagChildDType{},
                                               new AstBasicDType{$<fl>2, LOGIC_IMPLICIT, $1}}); }
        |       data_type rs_fId
                        { $$ = $2;
                          $$->fvarp(new AstVar{$<fl>1, VVarType::PORT, $2->name(), VFlagChildDType{},
                                               $1}); }
        |       yVOID rs_fId
                        { $$ = $2; }
        ;

rs_fId:  // IEEE: part of rs_production
                id
                        { $<fl>$ = $<fl>1;
                          $$ = new AstRSProd{$<fl>$, *$1, nullptr, nullptr}; }
        ;

rs_ruleList:  // IEEE: rs_rule+ part of rs_production
                rs_rule                                 { $$ = $1; }
        |       rs_ruleList '|' rs_rule                 { $$ = addNextNull($1, $3); }
        ;

rs_rule:  // ==IEEE: rs_rule
                rs_production_list
                        { $$ = new AstRSRule{$1->fileline(), nullptr, $1, nullptr}; }
        |       rs_production_list yP_COLONEQ rs_weight_specification
                        { $$ = new AstRSRule{$1->fileline(), $3, $1, nullptr}; }
        |       rs_production_list yP_COLONEQ rs_weight_specification rs_code_block
                        { $$ = new AstRSRule{$1->fileline(), $3, $1, $4}; }
        ;

rs_production_list:  // ==IEEE: rs_production_list
                rs_prodList
                        { $$ = new AstRSProdList{CRELINE(), nullptr, $1}; }
        |       yRAND yJOIN rs_production_item rs_production_itemList
                        { $$ = new AstRSProdList{$1, new AstConst{$2, AstConst::RealDouble{}, 0.5}, $3};
                          $$->randJoin(true);
                          $$->addProdsp($4); }
        |       yRAND yJOIN '(' expr ')' rs_production_item rs_production_itemList
                        { $$ = new AstRSProdList{$1, $4, $6};
                          $$->randJoin(true);
                          $$->addProdsp($7); }
        ;

rs_weight_specification:  // ==IEEE: rs_weight_specification
                intnumAsConst                           { $$ = $1; }
        |       idClassSel/*ps_identifier*/             { $$ = $1; }
        |       '(' expr ')'                            { $$ = $2; }
        ;

rs_code_block:  // ==IEEE: rs_code_block
                '{' '}'                                 { $$ = nullptr; }
        |       '{' rs_code_blockItemList '}'           { $$ = $2; }
        ;

rs_code_blockItemList:  // IEEE: part of rs_code_block
                rs_code_blockItem                       { $$ = $1; }
        |       rs_code_blockItemList rs_code_blockItem         { $$ = addNextNull($1, $2); }
        ;

rs_code_blockItem:  // IEEE: part of rs_code_block
                data_declaration                        { $$ = $1; }
        |       stmt                                    { $$ = $1; }
        ;

rs_prodList:  // IEEE: rs_prod+
                rs_prod                                 { $$ = $1; }
        |       rs_prodList rs_prod                     { $$ = addNextNull($1, $2); }
        ;

rs_prod:  // ==IEEE: rs_prod
                rs_production_item                      { $$ = $1; }
        |       rs_code_block                           { $$ = $1; }
        //                      // IEEE: rs_if_else
        |       yIF '(' expr ')' rs_production_item %prec prLOWER_THAN_ELSE
                        { $$ = new AstIf{$<fl>1, $3, $5, nullptr}; }
        |       yIF '(' expr ')' rs_production_item yELSE rs_production_item
                        { $$ = new AstIf{$<fl>1, $3, $5, $7}; }
        //                      // IEEE: rs_repeat
        |       yREPEAT '(' expr ')' rs_production_item
                               { $$ = new AstRepeat{$<fl>1, $3, $5}; }
        //                      // IEEE: rs_case
        |       yCASE '(' expr ')' rs_case_itemList yENDCASE
                        { $$ = new AstCase{$<fl>1, VCaseType::CT_RANDSEQUENCE, $3, $5}; }
        ;

rs_production_itemList:  // IEEE: rs_production_item+
                rs_production_item                         { $$ = $1; }
        |       rs_production_itemList rs_production_item  { $$ = addNextNull($1, $2); }
        ;

rs_production_item:  // ==IEEE: rs_production_item
                idAny/*production_identifier*/
                        { $$ = new AstRSProdItem{$<fl>1, *$1, nullptr}; }
        |       idAny/*production_identifier*/ '(' list_of_argumentsE ')'
                        { $$ = new AstRSProdItem{$<fl>1, *$1, $3}; }
        ;

rs_case_itemList:  // IEEE: rs_case_item+
                rs_case_item                            { $$ = $1; }
        |       rs_case_itemList rs_case_item           { $$ = addNextNull($1, $2); }
        ;

rs_case_item:  // ==IEEE: rs_case_item
                caseCondList ':' rs_production_item ';'
                        { $$ = new AstCaseItem{$<fl>1, $1, $3}; }
        |       yDEFAULT rs_production_item ';'
                        { $$ = new AstCaseItem{$<fl>1, nullptr, $2}; }
        |       yDEFAULT ':' rs_production_item ';'
                        { $$ = new AstCaseItem{$<fl>1, nullptr, $3}; }
        ;

//**********************************************************************
// Checker

checker_declaration:  // ==IEEE: part of checker_declaration
                checkerFront checker_port_listE ';'
                        checker_or_generate_itemListE yENDCHECKER endLabelE
                        { $$ = $1;
                          $1->modTrace(GRAMMARP->allTracingOn($1->fileline()));
                          if ($2) $1->addStmtsp($2);
                          if ($4) $1->addStmtsp($4);
                          GRAMMARP->endLabel($<fl>6, $1, $6); }
        ;

checkerFront:  // IEEE: part of checker_declaration
                yCHECKER idAny/*checker_identifier*/
                        { $$ = new AstModule{$<fl>2, *$2, PARSEP->libname(), AstModule::Checker{}};
                          $$->modTrace(GRAMMARP->allTracingOn($$->fileline()));
                          $$->timeunit(PARSEP->timeLastUnit());
                          PARSEP->rootp()->timeprecisionMerge($$->fileline(),
                                                              PARSEP->timeLastPrec());
                          $$->unconnectedDrive(PARSEP->unconnectedDrive()); }
        |       checkerFront sigAttrScope               { $$ = $1; }
        ;

checker_port_listE:  // IEEE: [ ( [ checker_port_list ] ) ]
                /* empty */                             { $$ = nullptr; }
        |       '(' ')'                                 { $$ = nullptr; }
        |       '('
        /*mid*/         { VARRESET_LIST(PORT); GRAMMARP->m_pinAnsi = true; }
        /*cont*/    checker_port_list ')'
                        { $$ = $3; }
        ;

checker_port_list:  // ==IEEE: checker_port_list
                checker_port_item                             { $$ = $1; }
        |       checker_port_list ',' checker_port_item       { $$ = addNextNull($1, $3); }
        ;

checker_port_item:  // IEEE: checker_port_item
                checker_port_itemFront checker_port_itemAssignment  { $$ = $2; }
        ;

checker_port_itemFront:  // IEEE: part of checker_port_item
                checker_port_directionE property_formal_typeNoDt
                        { VARDTYPE($2); }
        //                      // data_type_or_implicit
        |       checker_port_directionE data_type
                        { VARDTYPE($2); GRAMMARP->m_typedPropertyPort = true; }
        |       checker_port_directionE yVAR data_type
                        { VARDTYPE($3); GRAMMARP->m_typedPropertyPort = true; }
        |       checker_port_directionE yVAR implicit_typeE
                        { VARDTYPE($3); }
        |       checker_port_directionE implicit_typeE
                        { VARDTYPE($2); }
        ;

checker_port_directionE:  // IEEE: [ checker_port_direction ]
                /* empty */                             { VARIO(INPUT); }
        |       yINPUT                                  { VARIO(INPUT); }
        |       yOUTPUT                                 { VARIO(OUTPUT); }
        ;

checker_port_itemAssignment:  // IEEE: part of checker_port_direction
                id variable_dimensionListE
                        { $$ = new AstPort{CRELINE(), PINNUMINC(), *$1};
                          $$->addNext(VARDONEA($<fl>1, *$1, $2, nullptr)); }
        |       id variable_dimensionListE '=' property_actual_arg
                        { $$ = new AstPort{CRELINE(), PINNUMINC(), *$1};
                          $$->addNext(VARDONEA($<fl>1, *$1, $2, $4));
                          BBUNSUP($3, "Unsupported: checker port variable default value"); }
        ;

checker_or_generate_itemListE:  // IEEE: [{ checker_or_generate_itemList }]
                /* empty */                             { $$ = nullptr; }
        |       checker_or_generate_itemList            { $$ = $1; }
        ;

checker_or_generate_itemList:  // IEEE: { checker_or_generate_itemList }
                checker_or_generate_item                { $$ = $1; }
        |       checker_or_generate_itemList checker_or_generate_item   { $$ = addNextNull($1, $2); }
        ;

checker_or_generate_item:  // ==IEEE: checker_or_generate_item
                checker_or_generate_item_declaration    { $$ = $1; }
        |       initial_construct                       { $$ = $1; }
        //                      // IEEE: checker_construct
        |       always_construct                        { $$ = $1; }
        |       final_construct                         { $$ = $1; }
        |       assertion_item                          { $$ = $1; }
        |       continuous_assign                       { $$ = $1; }
        |       checker_generate_item                   { $$ = $1; }
        ;

checker_or_generate_item_declaration:  // ==IEEE: checker_or_generate_item_declaration
                data_declaration                        { $$ = $1; }
        |       yRAND data_declaration
                        { $$ = $2; BBUNSUP($1, "Unsupported: checker rand"); }
        |       function_declaration                    { $$ = $1; }
        |       checker_declaration
                        { $$ = nullptr; BBUNSUP($1, "Unsupported: recursive 'checker'"); DEL($1); }
        |       assertion_item_declaration              { $$ = $1; }
        |       covergroup_declaration                  { $$ = $1; }
        //      // IEEE deprecated: overload_declaration
        |       genvar_declaration                      { $$ = $1; }
        |       clocking_declaration                    { $$ = $1; }
        |       modDefaultClocking                      { $$ = $1; }
        |       defaultDisable                          { $$ = $1; }
        |       ';'                                     { $$ = nullptr; }
        ;

checker_generate_item:  // ==IEEE: checker_generate_item
        //                      // Specialized for checker so need "c_" prefixes here
                c_loop_generate_construct               { $$ = $1; }
        |       c_conditional_generate_construct        { $$ = $1; }
        |       c_generate_region                       { $$ = $1; }
        //
        |       severity_system_task                    { $$ = $1; }
        ;

//UNSUPchecker_instantiation<nodep>:
//UNSUP //                      // Only used for procedural_assertion_item's
//UNSUP //                      // Version in concurrent_assertion_item looks like etcInst
//UNSUP //                      // Thus instead of *_checker_port_connection we can use etcInst's instPinListE
//UNSUP         id/*checker_identifier*/ id '(' instPinListE ')' ';'     { }
//UNSUP ;

//**********************************************************************
// Class

class_declaration:       // ==IEEE: part of class_declaration
        //                      // IEEE-2012: using this also for interface_class_declaration
        //                      // The classExtendsE rule relies on classFront having the
        //                      // new class scope correct via classFront
                classFront parameter_port_listE classExtendsE classImplementsE ';'
        /*mid*/         { // Allow resolving types declared in base extends class
                          $1->hasParameterList($<flag>2);
                        }
        /*cont*/    class_itemListEnd endLabelE
                        { $$ = $1; $1->addMembersp($2);
                          $1->addExtendsp($3);
                          $1->addExtendsp($4);
                          $1->addMembersp($7);
                          GRAMMARP->endLabel($<fl>8, $1, $8); }
        ;

classFront:             // IEEE: part of class_declaration
        //                      // IEEE 1800-2023: lifetimeE replaced with final_specifierE
                classVirtualE yCLASS final_specifierE lifetimeE idAny/*class_identifier*/
                        { $$ = new AstClass{$2, *$5, PARSEP->libname()};
                          $$->baseOverride($3);
                          $$->isVirtual($1);
                          v3Global.setHasClasses(); }
        //                      // IEEE: part of interface_class_declaration
        //                      // IEEE 1800-2023: lifetimeE removed
        |       yINTERFACE yCLASS idAny/*class_identifier*/
                        { $$ = new AstClass{$2, *$3, PARSEP->libname()};
                          $$->isInterfaceClass(true);
                          v3Global.setHasClasses(); }
        ;

classVirtualE:
                /* empty */                             { $$ = false; }
        |       yVIRTUAL__CLASS                         { $$ = true; }
        ;

classExtendsE:           // IEEE: part of class_declaration
        //                      // The classExtendsE rule relies on classFront having the
        //                      // new class scope correct via classFront
                /* empty */                             { $$ = nullptr; }
        |       yEXTENDS classExtendsList               { $$ = $2; }
        ;

classExtendsList:        // IEEE: part of class_declaration
                classExtendsOne                         { $$ = $1; }
        |       classExtendsList ',' classExtendsOne    { $$ = addNextNull($1, $3); }
        ;

classExtendsOne:         // IEEE: part of class_declaration
                class_typeExtImpList
                        { $$ = new AstClassExtends{$1->fileline(), $1, GRAMMARP->m_inImplements}; }
        |       class_typeExtImpList '(' list_of_argumentsE ')'
                        { $$ = new AstClassExtends{$1->fileline(), $1, GRAMMARP->m_inImplements};
                          $$->addArgsp($3); }
        //                      // IEEE-2023: Added: yEXTENDS class_type '(' yDEFAULT ')'
        |       class_typeExtImpList '(' yDEFAULT ')'
                        { $$ = new AstClassExtends{$1->fileline(), $1, GRAMMARP->m_inImplements};
                          BBUNSUP($<fl>2, "Unsupported: 'extends' with 'default'"); }
        ;

classImplementsE:        // IEEE: part of class_declaration
        //                      // All 1800-2012
                /* empty */                             { $$ = nullptr; }
        |       yIMPLEMENTS
        /*mid*/         { GRAMMARP->m_inImplements = true; }
        /*cont*/    classImplementsList
                        { $$ = $3;
                          GRAMMARP->m_inImplements = false; }
        ;

classImplementsList:     // IEEE: part of class_declaration
        //                      // All 1800-2012
                classExtendsOne                         { $$ = $1; }
        |       classImplementsList ',' classExtendsOne
                        { $$ = addNextNull($1, $3); }
        ;

class_typeExtImpList:  // IEEE: class_type: "[package_scope] id [ parameter_value_assignment ]"
        //                      // but allow yaID__aTYPE for extends/implements
        //                      // If you follow the rules down, class_type is really a list via ps_class_identifier
                class_typeExtImpOne                     { $$ = $1; }
        |       class_typeExtImpList yP_COLONCOLON class_typeExtImpOne
                        { $$ = new AstDot{$<fl>1, true, $1, $3}; }
        ;

class_typeExtImpOne:  // part of IEEE: class_type, where we either get a package_scope component or class
        //                      // If you follow the rules down, class_type is really a list via ps_class_identifier
        //                      // Not listed in IEEE, but see bug627 any parameter type maybe a class
        //                      // If idAny below is a class, parameter_value is legal
        //                      // If idAny below is a package, parameter_value is not legal
        //                      // If idAny below is otherwise, not legal
                idAny
        /*mid*/         { /* no nextId as not refing it above this*/ }
        /*cont*/    parameter_value_assignmentClassE
                        { $$ = new AstClassOrPackageRef{$<fl>1, *$1, nullptr, $3}; }
        |       idCC
        /*mid*/         { /* no nextId as not refing it above this*/ }
        /*cont*/    parameter_value_assignmentClassE
                        { $$ = new AstClassOrPackageRef{$<fl>1, *$1, nullptr, $3}; }
        //
        //                      // package_sopeIdFollows expanded
        |       yD_UNIT yP_COLONCOLON
                        { $$ = new AstClassOrPackageRef{$<fl>1, "$unit", nullptr, nullptr}; }
        ;

//=========
// Package scoping - to traverse the symbol table properly, the final identifer
// must be included in the rules below.
// Each of these must end with {symsPackageDone | symsClassDone}

//=== Below rules assume special scoping per above

packageClassScopeNoId:  // IEEE: [package_scope] not followed by yaID
                packageClassScope                       { $$ = $1; }
        ;

packageClassScopeE:  // IEEE: [package_scope]
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // TODO: To support classes should return generic type, not packagep
        //                      // class_qualifier := [ yLOCAL '::'  ] [ implicit_class_handle '.'  class_scope ]
                /* empty */                             { $$ = nullptr; }
        |       packageClassScope                       { $$ = $1; }
        ;

packageClassScope:   // IEEE: class_scope
        //                      // IEEE: "class_type yP_COLONCOLON"
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // In this parser <package_identifier>:: and <class_identifier>:: are indistinguishible
                packageClassScopeList                   { $$ = $1; }
        |       localNextId yP_COLONCOLON               { $$ = $1; }
        |       dollarUnitNextId yP_COLONCOLON          { $$ = $1; }
        |       dollarUnitNextId yP_COLONCOLON packageClassScopeList
                        { $$ = new AstDot{$2, true, $1, $3}; }
        ;

packageClassScopeList:   // IEEE: class_type: "id [ parameter_value_assignment ]" but allow yaID__aTYPE
        //                      // Or IEEE: [package_scope]
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // In this parser <package_identifier>:: and <class_identifier>:: are indistinguishible
        //                      // If you follow the rules down, class_type is really a list via ps_class_identifier
                packageClassScopeItem                   { $$ = $1; }
        |       packageClassScopeList packageClassScopeItem
                        { $$ = new AstDot{$<fl>2, true, $1, $2}; }
        ;

packageClassScopeItem:   // IEEE: package_scope or [package_scope]::[class_scope]
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // IEEE: class_type: "id [ parameter_value_assignment ]" but allow yaID__aTYPE
        //                      //vv mid rule action needed otherwise we might not have NextId in time to parse the id token
                idCC
        /*mid*/         { }
        /*cont*/    yP_COLONCOLON
                        { $$ = new AstClassOrPackageRef{$<fl>1, *$1, nullptr, nullptr}; }
        //
        |       idCC parameter_value_assignmentClass
        /*mid*/         { }
        /*cont*/    yP_COLONCOLON
                        { $$ = new AstClassOrPackageRef{$<fl>1, *$1, nullptr, $2}; }
        ;

dollarUnitNextId:    // $unit
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // Must call nextId without any additional tokens following
                yD_UNIT
                        { $$ = new AstClassOrPackageRef{$1, "$unit", nullptr, nullptr}; }
        ;

localNextId:         // local::
        //                      // IMPORTANT: The lexer will parse the following ID to be in the found package
        //                      //     if not needed must use packageClassScopeNoId
        //                      // Must call nextId without any additional tokens following
                yLOCAL__COLONCOLON
                        { $$ = new AstClassOrPackageRef{$1, "local::", nullptr, nullptr}; }
        ;

//^^^=========

class_itemListEnd:
                yENDCLASS                               { $$ = nullptr; }
        |       class_itemList yENDCLASS                { $$ = $1; }
        |       error yENDCLASS                         { $$ = nullptr; }  // LCOV_EXCL_LINE
        |       class_itemList error yENDCLASS          { $$ = $1; }  // LCOV_EXCL_LINE
        ;

class_itemList:
                class_item                              { $$ = $1; }
        |       class_itemList class_item               { $$ = addNextNull($1, $2); }
        ;

class_item:                      // ==IEEE: class_item
                class_property                          { $$ = $1; }
        |       class_method                            { $$ = $1; }
        |       class_constraint                        { $$ = $1; }
        //
        |       class_declaration                       { $$ = $1; }
        |       timeunits_declaration                   { $$ = $1; }
        |       covergroup_declaration
                        {
                          const string cgName = $1->name();
                          $1->name("__vlAnonCG_" + cgName);
                          AstVar* const newp = new AstVar{$1->fileline(), VVarType::VAR, cgName,
                              VFlagChildDType{}, new AstRefDType($1->fileline(), $1->name())};
                          $$ = addNextNull($1, newp);
                        }
        //                      // local_parameter_declaration under parameter_declaration
        |       parameter_declaration ';'               { $$ = $1; }
        |       ';'                                     { $$ = nullptr; }
        //                      // Verilator specific
        |       vlScBlock                               { $$ = $1; }
        //
        |       error ';'                               { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

class_method:            // ==IEEE: class_method
                memberQualListE task_declaration        { $$ = $2; $1.applyToNodes($2); }
        |       memberQualListE function_declaration    { $$ = $2; $1.applyToNodes($2); }
        |       yPURE yVIRTUAL__ETC memberQualListE method_prototype ';'
                        { $$ = $4; $3.applyToNodes($4); $4->pureVirtual(true); $4->isVirtual(true); }
        |       yEXTERN memberQualListE method_prototype ';'
                        { $$ = $3; $2.applyToNodes($3); $3->isExternProto(true); }
        //                      // IEEE: "method_qualifierE class_constructor_declaration"
        //                      // part of function_declaration
        |       yEXTERN memberQualListE class_constructor_prototype
                        { $$ = $3; $2.applyToNodes($3); $3->isExternProto(true); }
        ;

dynamic_override_specifiersE:  // IEEE: dynamic_override_specifiers or empty
                /* empty */                             { $$ = VBaseOverride{}; }
        //                      // IEEE: Expanded [ initial_or_extends_specifier ] [ final_specifier ]
        //                      // Note lifetime used by members is instead under memberQual
        |       ':' yINITIAL                            { $$ = VBaseOverride{VBaseOverride::Initial{}}; }
        |       ':' yEXTENDS                            { $$ = VBaseOverride{VBaseOverride::Extends{}}; }
        |       ':' yINITIAL ':' yFINAL                 { $$ = VBaseOverride{VBaseOverride::Initial{}};
                                                          $$.combine(VBaseOverride{VBaseOverride::Final{}}); }
        |       ':' yEXTENDS ':' yFINAL                 { $$ = VBaseOverride{VBaseOverride::Extends{}};
                                                          $$.combine(VBaseOverride{VBaseOverride::Final{}}); }
        |       ':' yFINAL                              { $$ = VBaseOverride{VBaseOverride::Final{}}; }
        ;

final_specifierE:  // ==IEEE: final_specifier (similar to dynamic_override_specifiers)
                /* empty */                             { $$ = VBaseOverride{}; }
        |       ':' yFINAL                              { $$ = VBaseOverride{VBaseOverride::Final{}}; }
        ;

// IEEE: class_constructor_prototype
// See function_declaration

memberQualListE:    // Called from class_property for all qualifiers before yVAR
        //                      // Also before method declarations, to prevent grammar conflict
        //                      // Thus both types of qualifiers (method/property) are here
                /*empty*/                               { $$ = VMemberQualifiers::none(); }
        |       memberQualList                          { $$ = $1; }
        ;

memberQualList:
                memberQualOne                           { $$ = $1; }
        |       memberQualList memberQualOne            { $$ = VMemberQualifiers::combine($1, $2); }
        ;

memberQualOne:                      // IEEE: property_qualifier + method_qualifier
        //                      // Part of method_qualifier and property_qualifier
        //                      // IMPORTANT: yPROTECTED | yLOCAL is in a lex rule
                yPROTECTED                              { $$ = VMemberQualifiers::none(); $$.m_protected = true; }
        |       yLOCAL__ETC                             { $$ = VMemberQualifiers::none(); $$.m_local = true; }
        |       ySTATIC__ETC                            { $$ = VMemberQualifiers::none(); $$.m_static = true; }
        //                      // Part of method_qualifier only
        |       yVIRTUAL__ETC                           { $$ = VMemberQualifiers::none(); $$.m_virtual = true; }
        //                      // Part of property_qualifier only
        |       random_qualifier                        { $$ = $1; }
        //                      // Part of data_declaration, but not in data_declarationVarFrontClass
        |       yCONST__ETC                             { $$ = VMemberQualifiers::none(); $$.m_const = true; }
        ;

//**********************************************************************
// Constraints

class_constraint:  // ==IEEE: class_constraint
        //                      // IEEE: constraint_declaration
                constraintStaticE yCONSTRAINT dynamic_override_specifiersE constraintIdNew constraint_block
                        { $$ = $4; $$->isStatic($1); $$->baseOverride($3); $$->addItemsp($5); }
        //                      // IEEE: constraint_prototype + constraint_prototype_qualifier
        |       constraintStaticE yCONSTRAINT dynamic_override_specifiersE constraintIdNew ';'
                        { $$ = $4; $$->isStatic($1); $$->baseOverride($3);
                          $$->isExternProto(true); }
        |       yEXTERN constraintStaticE yCONSTRAINT dynamic_override_specifiersE constraintIdNew ';'
                        { $$ = $5; $$->isStatic($2); $$->baseOverride($4);
                          $$->isExternProto(true); $$->isExternExplicit(true); }
        |       yPURE constraintStaticE yCONSTRAINT constraintIdNew ';'
                        { $$ = $4; $$->isKwdPure($1); $$->isStatic($2); }
        ;

constraintIdNew:  // IEEE: id part of class_constraint
                idAny/*constraint_identifier*/
                        { $$ = new AstConstraint{$<fl>1, *$1, nullptr}; }
        ;

constraint_block:  // ==IEEE: constraint_block
                '{' '}'                                         { $$ = nullptr; }
        |       '{' constraint_block_itemList '}'               { $$ = $2; }
        //
        |       '{' error '}'                                   { $$ = nullptr; }  // LCOV_EXCL_LINE
        |       '{' constraint_block_itemList error '}'         { $$ = $2; }  // LCOV_EXCL_LINE
        ;

constraint_block_itemList:  // IEEE: { constraint_block_item }
                constraint_block_item                           { $$ = $1; }
        |       constraint_block_itemList constraint_block_item { $$ = addNextNull($1, $2); }
        ;

constraint_block_item:  // ==IEEE: constraint_block_item
                constraint_expression                           { $$ = $1; }
        |       ySOLVE solve_before_list yBEFORE solve_before_list ';'
                        { $$ = new AstConstraintBefore{$1, $2, $4}; }
        ;

solve_before_list:  // ==IEEE: solve_before_list
                constraint_primary                              { $$ = $1; }
        |       solve_before_list ',' constraint_primary        { $$ = addNextNull($1, $3); }
        ;

constraint_primary:  // ==IEEE: constraint_primary
        //                      // exprScope more general than:
        //                      // [ implicit_class_handle '.' | class_scope ] hierarchical_identifier select [ '(' ')' ]
                exprScope                                       { $$ = $1; }
        ;

constraint_expressionList:  // ==IEEE: { constraint_expression }
                constraint_expression                           { $$ = $1; }
        |       constraint_expressionList constraint_expression { $$ = addNextNull($1, $2); }
        ;

constraint_expression:  // ==IEEE: constraint_expression
                expr/*expression_or_dist*/ ';'
                        { $$ = new AstConstraintExpr{$1->fileline(), $1}; }
        //                      // 1800-2012:
        |       ySOFT expr/*expression_or_dist*/ ';'
                        { AstConstraintExpr* const newp = new AstConstraintExpr{$1, $2};
                          newp->isSoft(true);
                          $$ = newp; }
        //                      // 1800-2012:
        //                      // IEEE: uniqueness_constraint ';'
        |       yUNIQUE '{' range_list '}' ';'
                        { $$ = new AstConstraintUnique{$1, $3}; }
        //                      // IEEE: expr yP_MINUSGT constraint_set
        //                      // Conflicts with expr:"expr yP_MINUSGT expr"; rule moved there
        //
        |       yIF '(' expr ')' constraint_set %prec prLOWER_THAN_ELSE
                        { $$ = new AstConstraintIf{$1, $3, $5, nullptr}; }
        |       yIF '(' expr ')' constraint_set yELSE constraint_set
                        { $$ = new AstConstraintIf{$1, $3, $5, $7}; }
        //                      // IEEE says array_identifier here, but dotted accepted in VMM + 1800-2009
        |       yFOREACH '(' idClassSelForeach ')' constraint_set
                        { $$ = new AstConstraintForeach{$1, $3, $5}; }
        //                      // soft is 1800-2012
        |       yDISABLE ySOFT expr/*constraint_primary*/ ';'
                        { AstConstraintExpr* const newp = new AstConstraintExpr{$1, $3};
                          newp->isDisableSoft(true);
                          $$ = newp; }
        //
        |       error ';'
                        { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

constraint_set:  // ==IEEE: constraint_set
                constraint_expression                   { $$ = $1; }
        |       '{' constraint_expressionList '}'       { $$ = $2; }
        //
        |       '{' error '}'                           { $$ = nullptr; }  // LCOV_EXCL_LINE
        |       '{' constraint_expressionList error '}' { $$ = $2; }  // LCOV_EXCL_LINE
        ;

dist_list:  // ==IEEE: dist_list
                dist_item                               { $$ = $1; }
        |       dist_list ',' dist_item                 { $$ = addNextNull($1, $3); }
        ;

dist_item:  // ==IEEE: dist_item + dist_weight
                value_range
                        { $$ = new AstDistItem{$1->fileline(), $1, new AstConst{$1->fileline(), 1}}; }
        |       value_range yP_COLONEQ  expr
                        { $$ = new AstDistItem{$2, $1, $3}; }
        |       value_range yP_COLONDIV expr
                        { $$ = new AstDistItem{$2, $1, $3}; $$->isWhole(true); }
        //                      // IEEE 1800-2023 added:
        |       yDEFAULT yP_COLONDIV expr
                        { BBUNSUP($<fl>2, "Unsupported: 'default :/' constraint");
                          $$ = nullptr; DEL($3); }
        ;

extern_constraint_declaration:  // ==IEEE: extern_constraint_declaration
                constraintStaticE yCONSTRAINT dynamic_override_specifiersE packageClassScopeE constraintIdNew constraint_block
                        { $$ = $5; $$->isStatic($1); $$->isExternDef(true);
                          $$->baseOverride($3); $$->classOrPackagep($4); $$->addItemsp($6); }
        ;

constraintStaticE:  // IEEE: part of extern_constraint_declaration
                /* empty */                             { $$ = false; }
        |       ySTATIC__CONSTRAINT                     { $$ = true; }
        ;

//**********************************************************************
// Constants

timeNumAdjusted:         // Time constant, adjusted to module's time units/precision
                yaTIMENUM
                        { $$ = new AstTimeImport{$<fl>1, new AstConst{$<fl>1, AstConst::RealDouble{}, $1}}; }
        ;

//**********************************************************************
// Generic tokens

colon:                      // Generic colon that isn't making a label (e.g. in a case_item)
                ':'                                     { $$ = $1; }
        |       yP_COLON__BEGIN                         { $$ = $1; }
        |       yP_COLON__FORK                          { $$ = $1; }
        ;

//**********************************************************************
// Config - config...endconfig

config_declaration:  // == IEEE: config_declaration
                yCONFIG idAny/*config_identifier*/ ';'
        /*cont*/    configParameterListE design_statement config_rule_statementListE
        /*cont*/    yENDCONFIG endLabelE
                { AstConfig* const newp = new AstConfig{$1, PARSEP->libname(), *$2};
                  newp->addDesignp($5);
                  newp->addItemsp($4);
                  newp->addItemsp($6);
                  GRAMMARP->endLabel($<fl>7, *$2, $8);
                  PARSEP->rootp()->addMiscsp(newp); }
        ;

configParameterListE:  // IEEE: { local_parameter_declaration ';' }
                /* empty */                             { $$ = nullptr; }
        |       configParameterList                     { $$ = $1; }
        ;

configParameterList:  // IEEE: part of config_declaration
                configParameter                         { $$ = nullptr; DEL($1); }
        |       configParameterList configParameter     { $$ = addNextNull($1, $2); }
        ;

configParameter:  // IEEE: part of config_declaration
                parameter_declaration ';'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: config localparam declaration"); DEL($1); }
        ;

design_statement:  // == IEEE: design_statement
                yDESIGN configCellList ';'              { $$ = $2; }
        ;

configCellList:  // IEEE: part of design_statement
                configCell                              { $$ = $1; }
        |       configCellList configCell               { $$ = addNextNull($1, $2); }
        ;

configCell:  // IEEE: part of design_statement, part of cell_clause
                idAny/*cell_identifier*/
                        { $$ = new AstConfigCell{$<fl>1, PARSEP->libname(), *$1}; }
        |       idAny/*library_identifier*/ '.' idAny/*cell_identifier*/
                        { $$ = new AstConfigCell{$<fl>1, *$1, *$3}; }
        ;

config_rule_statementListE:  // IEEE: { config_rule }
                /* empty */                             { $$ = nullptr; }
        |       config_rule_statementList               { $$ = $1; }
        ;

config_rule_statementList:  // IEEE: { config_rule }
                config_rule_statement                   { $$ = $1; }
        |       config_rule_statementList config_rule_statement   { $$ = addNextNull($1, $2); }
        ;

config_rule_statement:  // == IEEE: config_rule_statement
        //                      // IEEE: default_clause
                yDEFAULT liblist_clause ';'
                        { $$ = new AstConfigRule{$1, nullptr, $2, false}; }
        //                      // IEEE: inst_clause
        |       yINSTANCE inst_name liblist_clause ';'
                        { $$ = new AstConfigRule{$1, $2, $3, false}; }
        |       yINSTANCE inst_name use_clause ';'
                        { $$ = new AstConfigRule{$1, $2, $3, false}; }
        //                      // IEEE: cell_clause
        |       yCELL configCell liblist_clause ';'
                        { $$ = new AstConfigRule{$1, $2, $3, true}; }
        |       yCELL configCell use_clause ';'
                        { $$ = new AstConfigRule{$1, $2, $3, true}; }
        |       error ';'
                        { $$ = nullptr; }  // LCOV_EXCL_LINE
        ;

inst_name:  // == IEEE: inst_name
                idAnyAsParseRef/*topmodule_identifier*/
                        { $$ = $1; }
        |       idAnyAsParseRef/*topmodule_identifier*/ inst_nameInstanceList
                        { $$ = new AstDot{$<fl>1, false, $1, $2}; }
        ;

inst_nameInstanceList:  // IEEE: part of inst_name
                '.' idAnyAsParseRef/*instance_identifier*/
                        { $$ = $2; }
        |       inst_nameInstanceList '.' idAnyAsParseRef/*instance_identifier*/
                        { $$ = new AstDot{$<fl>2, false, $1, $3}; }
        ;

liblist_clause:  // == IEEE: liblist_clause
                yLIBLIST                                { $$ = nullptr; }
        |       yLIBLIST liblistLibraryList             { $$ = $2; }
        ;

liblistLibraryList:  // IEEE: part of liblist_clause
                idAnyAsParseRef/*library_identifier*/
                        { $$ = $1; }
        |       liblistLibraryList idAnyAsParseRef/*library_identifier*/
                        { $$ = addNextNull($1, $2); }
        ;

use_clause:  // == IEEE: use_clause
                yUSE idAny/*cell_identifier*/ useAssignmentListE colonConfigE
                        { $$ = new AstConfigUse{$1, "", *$2, $3, $4}; }
        |       yUSE idAny/*library_identifier*/ '.' idAny/*cell_identifier*/ useAssignmentListE colonConfigE
                        { $$ = new AstConfigUse{$1, *$2, *$4, $5, $6}; }
        |       yUSE useAssignmentListE colonConfigE
                        { $$ = new AstConfigUse{$1, "", "", $2, $3}; }
        ;

useAssignmentListE:  // IEEE: part of use clause
                /* empty */                             { $$ = nullptr; }
        //                      // IEEE is missing the '#' '(', but examples need it
        |       '#' '(' ')'                             { $$ = nullptr; }
        |       '#' '(' useAssignmentList ')'           { $$ = $3; }
        ;

useAssignmentList:  // IEEE: part of use_clause
                useAssignment                           { $$ = $1; }
        |       useAssignmentList ',' useAssignment     { $$ = addNextNull($1, $3); }
        ;

useAssignment:  // IEEE: part of use_clause
        //                      // IEEE: named_parameter_assignment
                '.' idAny/*parameter_identifier*/ '(' ')'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: 'config use' parameter assignment"); }
        |       '.' idAny/*parameter_identifier*/ '(' exprOrDataType ')'
                        { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: 'config use' parameter assignment"); DEL($4); }
        ;

colonConfigE:  // IEEE: [ ':' yCONFIG]
                /* empty */                             { $$ = false; }
        |       ':' yCONFIG                             { $$ = true; }
        ;

//**********************************************************************
// Config - lib.map
//

library_declaration:  // IEEE: library_declaration
                yLIBRARY yaSTRING file_path_specList incdirE ';'
                        { $$ = new AstLibrary{$<fl>1, *$2, $3, $4}; }
        ;
incdirE:  // IEEE: [ '-' yINCDIR file_path_specList ';']
                /* empty */                             { $$ = nullptr; }
                                // https://accellera.mantishub.io/view.php?id=1166
        |       yINCDIR file_path_specList              { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: config incdir"); }
        ;
include_statement:  // IEEE: include_statement
                yINCLUDE file_path_spec ';'             { $$ = nullptr; BBUNSUP($<fl>1, "Unsupported: config include"); }
        ;
file_path_specList:  // IEEE: file_path_spec { ',' file_path_spec }
                file_path_spec                          { $$ = $1; }
        |       file_path_specList ',' file_path_spec   { $$ = addNextNull($1, $3); }
        ;
file_path_spec:  // IEEE: file_path_spec
                yaSTRING { $$ = new AstParseRef{$<fl>1, *$1}; }
        ;

//**********************************************************************
// VLT Files

vltItem:
        //                      // TODO support arbitrary order of arguments
                vltOffFront
                        { V3Control::addIgnore($1, false, "*", 0, 0); }
        |       vltOffFront vltDFile
                        { V3Control::addIgnore($1, false, *$2, 0, 0); }
        |       vltOffFront vltDFile yVLT_D_LINES yaINTNUM
                        { V3Control::addIgnore($1, false, *$2, $4->toUInt(), $4->toUInt()); }
        |       vltOffFront vltDFile yVLT_D_LINES yaINTNUM '-' yaINTNUM
                        { V3Control::addIgnore($1, false, *$2, $4->toUInt(), $6->toUInt()); }
        |       vltOffFront vltDFile vltDMatch
                        { if (($1 == V3ErrorCode::I_COVERAGE) || ($1 == V3ErrorCode::I_TRACING)) {
                              $<fl>1->v3error("Argument -match only supported for lint_off");
                          } else {
                              V3Control::addIgnoreMatch($1, *$2, "", *$3);
                          }}
        |       vltOffFront vltDFile vltDContents
                        { if (($1 == V3ErrorCode::I_COVERAGE) || ($1 == V3ErrorCode::I_TRACING)) {
                              $<fl>1->v3error("Argument -match only supported for lint_off");
                          } else {
                              V3Control::addIgnoreMatch($1, *$2, *$3, "*");
                          }}
        |       vltOffFront vltDFile vltDContents vltDMatch
                        { if (($1 == V3ErrorCode::I_COVERAGE) || ($1 == V3ErrorCode::I_TRACING)) {
                              $<fl>1->v3error("Argument -match only supported for lint_off");
                          } else {
                              V3Control::addIgnoreMatch($1, *$2, *$3, *$4);
                          }}
        |       vltOffFront vltDScope
                        { if ($1 != V3ErrorCode::I_TRACING) {
                              $<fl>1->v3error("Argument -scope only supported for tracing_on/off");
                          } else {
                              V3Control::addScopeTraceOn(false, *$2, 0);
                          }}
        |       vltOffFront vltDScope vltDLevels
                        { if ($1 != V3ErrorCode::I_TRACING) {
                              $<fl>1->v3error("Argument -scope only supported for tracing_on/off_off");
                          } else {
                              V3Control::addScopeTraceOn(false, *$2, $3->toUInt());
                          }}
        |       vltOnFront
                        { V3Control::addIgnore($1, true, "*", 0, 0); }
        |       vltOnFront vltDFile
                        { V3Control::addIgnore($1, true, *$2, 0, 0); }
        |       vltOnFront vltDFile yVLT_D_LINES yaINTNUM
                        { V3Control::addIgnore($1, true, *$2, $4->toUInt(), $4->toUInt()); }
        |       vltOnFront vltDFile yVLT_D_LINES yaINTNUM '-' yaINTNUM
                        { V3Control::addIgnore($1, true, *$2, $4->toUInt(), $6->toUInt()); }
        |       vltOnFront vltDScope
                        { if ($1 != V3ErrorCode::I_TRACING) {
                              $<fl>1->v3error("Argument -scope only supported for tracing_on/off");
                          } else {
                              V3Control::addScopeTraceOn(true, *$2, 0);
                          }}
        |       vltOnFront vltDScope vltDLevels
                        { if ($1 != V3ErrorCode::I_TRACING) {
                              $<fl>1->v3error("Argument -scope only supported for tracing_on/off_off");
                          } else {
                              V3Control::addScopeTraceOn(true, *$2, $3->toUInt());
                          }}
        |       vltVarAttrFront vltDModuleE vltDFTaskE vltVarAttrSpecE attr_event_controlE
                        { V3Control::addVarAttr($<fl>1, *$2, *$3, GRAMMARP->m_vltVarSpecKind, *$4, $1, $5); }
        |       vltVarAttrFrontDeprecated vltDModuleE vltDFTaskE vltVarAttrSpecE
                        { /* Historical, now has no effect */ }
        |       vltInlineFront vltDModuleE vltDFTaskE
                        { V3Control::addInline($<fl>1, *$2, *$3, $1); }
        |       yVLT_COVERAGE_BLOCK_OFF vltDFile
                        { V3Control::addCoverageBlockOff(*$2, 0); }
        |       yVLT_COVERAGE_BLOCK_OFF vltDFile yVLT_D_LINES yaINTNUM
                        { V3Control::addCoverageBlockOff(*$2, $4->toUInt()); }
        |       yVLT_COVERAGE_BLOCK_OFF vltDModule vltDBlock
                        { V3Control::addCoverageBlockOff(*$2, *$3); }
        |       yVLT_FULL_CASE vltDFile
                        { V3Control::addCaseFull(*$2, 0); }
        |       yVLT_FULL_CASE vltDFile yVLT_D_LINES yaINTNUM
                        { V3Control::addCaseFull(*$2, $4->toUInt()); }
        |       yVLT_HIER_BLOCK vltDModuleE
                        { V3Control::addModulePragma(*$2, VPragmaType::HIER_BLOCK); }
        |       yVLT_HIER_PARAMS vltDModuleE
                        { V3Control::addModulePragma(*$2, VPragmaType::HIER_PARAMS); }
        |       yVLT_HIER_WORKERS vltDModuleE vltDWorkers
                        { V3Control::addHierWorkers($<fl>1, *$2, $3->toSInt()); }
        |       yVLT_HIER_WORKERS vltDHierDpi vltDWorkers
                        { V3Control::addHierWorkers($<fl>1, *$2, $3->toSInt()); }
        |       yVLT_PARALLEL_CASE vltDFile
                        { V3Control::addCaseParallel(*$2, 0); }
        |       yVLT_PARALLEL_CASE vltDFile yVLT_D_LINES yaINTNUM
                        { V3Control::addCaseParallel(*$2, $4->toUInt()); }
        |       yVLT_PROFILE_DATA vltDHierDpi vltDCost
                        { V3Control::addProfileData($<fl>1, *$2, $3->toUQuad()); }
        |       yVLT_PROFILE_DATA vltDModel vltDMtask vltDCost
                        { V3Control::addProfileData($<fl>1, *$2, *$3, $4->toUQuad()); }
        ;

vltOffFront:
                yVLT_COVERAGE_OFF                       { $$ = V3ErrorCode::I_COVERAGE; }
        |       yVLT_TIMING_OFF                         { $$ = V3ErrorCode::I_TIMING; }
        |       yVLT_TRACING_OFF                        { $$ = V3ErrorCode::I_TRACING; }
        |       yVLT_LINT_OFF                           { $$ = V3ErrorCode::I_LINT; }
        |       yVLT_LINT_OFF yVLT_D_RULE idAny
                        { $$ = V3ErrorCode{*$3};
                          if ($$ == V3ErrorCode::EC_ERROR) $1->v3error("Unknown error code: '" << *$3 << "'"); }
        ;

vltOnFront:
                yVLT_COVERAGE_ON                        { $$ = V3ErrorCode::I_COVERAGE; }
        |       yVLT_TIMING_ON                          { $$ = V3ErrorCode::I_TIMING; }
        |       yVLT_TRACING_ON                         { $$ = V3ErrorCode::I_TRACING; }
        |       yVLT_LINT_ON                            { $$ = V3ErrorCode::I_LINT; }
        |       yVLT_LINT_ON yVLT_D_RULE idAny
                        { $$ = V3ErrorCode{*$3};
                          if ($$ == V3ErrorCode::EC_ERROR) $1->v3error("Unknown error code: '" << *$3 << "'"); }
        ;

vltDBlock:  // --block <arg>
                yVLT_D_BLOCK str                        { $$ = $2; }
        ;

vltDContents:
                yVLT_D_CONTENTS str                     { $$ = $2; }
        ;

vltDCost:  // --cost <arg>
                yVLT_D_COST yaINTNUM                    { $$ = $2; }
        ;

vltDFile:  // --file <arg>
                yVLT_D_FILE str                         { $$ = $2; }
        ;

vltDHierDpi:  // --hier-dpi <arg>
                yVLT_D_HIER_DPI str                     { $$ = $2; }
        ;

vltDLevels:  // --levels <arg>
                yVLT_D_LEVELS yaINTNUM                  { $$ = $2; }
        ;

vltDMatch:  // --match <arg>
                yVLT_D_MATCH str                        { $$ = $2; }
        ;

vltDModel:  // --model <arg>
                yVLT_D_MODEL str                        { $$ = $2; }
        ;

vltDMtask:  // --mtask <arg>
                yVLT_D_MTASK str                        { $$ = $2; }
        ;

vltDModule:  // --module <arg>
                yVLT_D_MODULE str                       { $$ = $2; }
        ;

vltDModuleE:  // [--module <arg>]
                /* empty */
                        { static string unit = "$unit"; $$ = &unit; }  // .vlt uses prettyName
        |       vltDModule
                        { $$ = $1; }
        ;

vltDScope:  // --scope <arg>
                yVLT_D_SCOPE str                        { $$ = $2; }
        ;

vltDFTaskE:
                /* empty */                             { static string empty; $$ = &empty; }
        |       yVLT_D_FUNCTION str                     { $$ = $2; }
        |       yVLT_D_TASK str                         { $$ = $2; }
        ;

vltDWorkers:  // --workers <arg>
                yVLT_D_WORKERS yaINTNUM                  { $$ = $2; }
        ;

vltInlineFront:
                yVLT_INLINE                             { $$ = true; }
        |       yVLT_NO_INLINE                          { $$ = false; }
        ;

vltVarAttrSpecE:
                /* empty */
                        { GRAMMARP->m_vltVarSpecKind = V3Control::VarSpecKind::VAR; static std::string empty; $$ = &empty; }
        |       yVLT_D_PARAM str
                        { GRAMMARP->m_vltVarSpecKind = V3Control::VarSpecKind::PARAM; $$ = $2; }
        |       yVLT_D_PORT str
                        { GRAMMARP->m_vltVarSpecKind = V3Control::VarSpecKind::PORT; $$ = $2; }
        |       yVLT_D_VAR str
                        { GRAMMARP->m_vltVarSpecKind = V3Control::VarSpecKind::VAR; $$ = $2; }
        ;

vltVarAttrFront:
                yVLT_ISOLATE_ASSIGNMENTS    { $$ = VAttrType::VAR_ISOLATE_ASSIGNMENTS; }
        |       yVLT_FORCEABLE              { $$ = VAttrType::VAR_FORCEABLE; }
        |       yVLT_PUBLIC                 { $$ = VAttrType::VAR_PUBLIC; v3Global.dpi(true); }
        |       yVLT_PUBLIC_FLAT            { $$ = VAttrType::VAR_PUBLIC_FLAT; v3Global.dpi(true); }
        |       yVLT_PUBLIC_FLAT_RD         { $$ = VAttrType::VAR_PUBLIC_FLAT_RD; v3Global.dpi(true); }
        |       yVLT_PUBLIC_FLAT_RW         { $$ = VAttrType::VAR_PUBLIC_FLAT_RW; v3Global.dpi(true); }
        |       yVLT_SC_BIGUINT             { $$ = VAttrType::VAR_SC_BIGUINT; }
        |       yVLT_SC_BV                  { $$ = VAttrType::VAR_SC_BV; }
        |       yVLT_SFORMAT                { $$ = VAttrType::VAR_SFORMAT; }
        |       yVLT_SPLIT_VAR              { $$ = VAttrType::VAR_SPLIT_VAR; }
        ;

vltVarAttrFrontDeprecated:
                yVLT_CLOCK_ENABLE           { }
        |       yVLT_CLOCKER                { }
        |       yVLT_NO_CLOCKER             { }
        ;

//**********************************************************************
%%
// For implementation functions see V3ParseGrammar.cpp

//YACC = /kits/sources/bison-2.4.1/src/bison --report=lookahead
// --report=lookahead
// --report=itemset
// --graph
