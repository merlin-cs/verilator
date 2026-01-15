/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_YY_HOME_RUNNER_WORK_VERILATOR_VERILATOR_CODEQL_BUILD_DIR_SRC_V3PARSEBISON_PRETMP_H_INCLUDED
# define YY_YY_HOME_RUNNER_WORK_VERILATOR_VERILATOR_CODEQL_BUILD_DIR_SRC_V3PARSEBISON_PRETMP_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    yaFLOATNUM = 258,              /* "FLOATING-POINT NUMBER"  */
    yaID__ETC = 259,               /* "IDENTIFIER"  */
    yaID__CC = 260,                /* "IDENTIFIER-::"  */
    yaID__LEX = 261,               /* "IDENTIFIER-in-lex"  */
    yaID__PATHPULSE = 262,         /* "IDENTIFIER-for-pathpulse"  */
    yaID__aINST = 263,             /* "IDENTIFIER-for-instance"  */
    yaID__aTYPE = 264,             /* "IDENTIFIER-for-type"  */
    yaINTNUM = 265,                /* "INTEGER NUMBER"  */
    yaTIMENUM = 266,               /* "TIME NUMBER"  */
    yaSTRING = 267,                /* "STRING"  */
    yaSTRING__IGNORE = 268,        /* "STRING-ignored"  */
    yaEDGEDESC = 269,              /* "EDGE DESCRIPTOR"  */
    yaTIMINGSPEC = 270,            /* "TIMING SPEC ELEMENT"  */
    ygenSTRENGTH = 271,            /* "STRENGTH keyword (strong1/etc)"  */
    yaTABLE_FIELD = 272,           /* "UDP table field"  */
    yaTABLE_LRSEP = 273,           /* ":"  */
    yaTABLE_LINEEND = 274,         /* "UDP table line end"  */
    yaSCCTOR = 275,                /* "`systemc_ctor block"  */
    yaSCDTOR = 276,                /* "`systemc_dtor block"  */
    yaSCHDR = 277,                 /* "`systemc_header block"  */
    yaSCHDRP = 278,                /* "`systemc_header_post block"  */
    yaSCIMP = 279,                 /* "`systemc_implementation block"  */
    yaSCIMPH = 280,                /* "`systemc_imp_header block"  */
    yaSCINT = 281,                 /* "`systemc_interface block"  */
    yVLT_CLOCKER = 282,            /* "clocker"  */
    yVLT_CLOCK_ENABLE = 283,       /* "clock_enable"  */
    yVLT_COVERAGE_BLOCK_OFF = 284, /* "coverage_block_off"  */
    yVLT_COVERAGE_OFF = 285,       /* "coverage_off"  */
    yVLT_COVERAGE_ON = 286,        /* "coverage_on"  */
    yVLT_FORCEABLE = 287,          /* "forceable"  */
    yVLT_FULL_CASE = 288,          /* "full_case"  */
    yVLT_HIER_BLOCK = 289,         /* "hier_block"  */
    yVLT_HIER_PARAMS = 290,        /* "hier_params"  */
    yVLT_HIER_WORKERS = 291,       /* "hier_workers"  */
    yVLT_INLINE = 292,             /* "inline"  */
    yVLT_ISOLATE_ASSIGNMENTS = 293, /* "isolate_assignments"  */
    yVLT_LINT_OFF = 294,           /* "lint_off"  */
    yVLT_LINT_ON = 295,            /* "lint_on"  */
    yVLT_NO_CLOCKER = 296,         /* "no_clocker"  */
    yVLT_NO_INLINE = 297,          /* "no_inline"  */
    yVLT_PARALLEL_CASE = 298,      /* "parallel_case"  */
    yVLT_PROFILE_DATA = 299,       /* "profile_data"  */
    yVLT_PUBLIC = 300,             /* "public"  */
    yVLT_PUBLIC_FLAT = 301,        /* "public_flat"  */
    yVLT_PUBLIC_FLAT_RD = 302,     /* "public_flat_rd"  */
    yVLT_PUBLIC_FLAT_RW = 303,     /* "public_flat_rw"  */
    yVLT_PUBLIC_MODULE = 304,      /* "public_module"  */
    yVLT_SC_BIGUINT = 305,         /* "sc_biguint"  */
    yVLT_SC_BV = 306,              /* "sc_bv"  */
    yVLT_SFORMAT = 307,            /* "sformat"  */
    yVLT_SPLIT_VAR = 308,          /* "split_var"  */
    yVLT_TIMING_OFF = 309,         /* "timing_off"  */
    yVLT_TIMING_ON = 310,          /* "timing_on"  */
    yVLT_TRACING_OFF = 311,        /* "tracing_off"  */
    yVLT_TRACING_ON = 312,         /* "tracing_on"  */
    yVLT_D_BLOCK = 313,            /* "--block"  */
    yVLT_D_CONTENTS = 314,         /* "--contents"  */
    yVLT_D_COST = 315,             /* "--cost"  */
    yVLT_D_FILE = 316,             /* "--file"  */
    yVLT_D_FUNCTION = 317,         /* "--function"  */
    yVLT_D_HIER_DPI = 318,         /* "--hier-dpi"  */
    yVLT_D_LEVELS = 319,           /* "--levels"  */
    yVLT_D_LINES = 320,            /* "--lines"  */
    yVLT_D_MATCH = 321,            /* "--match"  */
    yVLT_D_MODEL = 322,            /* "--model"  */
    yVLT_D_MODULE = 323,           /* "--module"  */
    yVLT_D_MTASK = 324,            /* "--mtask"  */
    yVLT_D_PARAM = 325,            /* "--param"  */
    yVLT_D_PORT = 326,             /* "--port"  */
    yVLT_D_RULE = 327,             /* "--rule"  */
    yVLT_D_SCOPE = 328,            /* "--scope"  */
    yVLT_D_TASK = 329,             /* "--task"  */
    yVLT_D_VAR = 330,              /* "--var"  */
    yVLT_D_WORKERS = 331,          /* "--workers"  */
    yaD_PLI = 332,                 /* "${pli-system}"  */
    yaT_NOUNCONNECTED = 333,       /* "`nounconnecteddrive"  */
    yaT_RESETALL = 334,            /* "`resetall"  */
    yaT_UNCONNECTED_PULL0 = 335,   /* "`unconnected_drive pull0"  */
    yaT_UNCONNECTED_PULL1 = 336,   /* "`unconnected_drive pull1"  */
    y1STEP = 337,                  /* "1step"  */
    yACCEPT_ON = 338,              /* "accept_on"  */
    yALIAS = 339,                  /* "alias"  */
    yALWAYS = 340,                 /* "always"  */
    yALWAYS_COMB = 341,            /* "always_comb"  */
    yALWAYS_FF = 342,              /* "always_ff"  */
    yALWAYS_LATCH = 343,           /* "always_latch"  */
    yAND = 344,                    /* "and"  */
    yASSERT = 345,                 /* "assert"  */
    yASSIGN = 346,                 /* "assign"  */
    yASSUME = 347,                 /* "assume"  */
    yAUTOMATIC = 348,              /* "automatic"  */
    yBEFORE = 349,                 /* "before"  */
    yBEGIN = 350,                  /* "begin"  */
    yBIND = 351,                   /* "bind"  */
    yBINS = 352,                   /* "bins"  */
    yBINSOF = 353,                 /* "binsof"  */
    yBIT = 354,                    /* "bit"  */
    yBREAK = 355,                  /* "break"  */
    yBUF = 356,                    /* "buf"  */
    yBUFIF0 = 357,                 /* "bufif0"  */
    yBUFIF1 = 358,                 /* "bufif1"  */
    yBYTE = 359,                   /* "byte"  */
    yCASE = 360,                   /* "case"  */
    yCASEX = 361,                  /* "casex"  */
    yCASEZ = 362,                  /* "casez"  */
    yCELL = 363,                   /* "cell"  */
    yCHANDLE = 364,                /* "chandle"  */
    yCHECKER = 365,                /* "checker"  */
    yCLASS = 366,                  /* "class"  */
    yCLOCKING = 367,               /* "clocking"  */
    yCMOS = 368,                   /* "cmos"  */
    yCONFIG = 369,                 /* "config"  */
    yCONSTRAINT = 370,             /* "constraint"  */
    yCONST__ETC = 371,             /* "const"  */
    yCONST__LEX = 372,             /* "const-in-lex"  */
    yCONST__REF = 373,             /* "const-then-ref"  */
    yCONTEXT = 374,                /* "context"  */
    yCONTINUE = 375,               /* "continue"  */
    yCOVER = 376,                  /* "cover"  */
    yCOVERGROUP = 377,             /* "covergroup"  */
    yCOVERPOINT = 378,             /* "coverpoint"  */
    yCROSS = 379,                  /* "cross"  */
    yDEASSIGN = 380,               /* "deassign"  */
    yDEFAULT = 381,                /* "default"  */
    yDEFPARAM = 382,               /* "defparam"  */
    yDESIGN = 383,                 /* "design"  */
    yDISABLE = 384,                /* "disable"  */
    yDIST = 385,                   /* "dist"  */
    yDO = 386,                     /* "do"  */
    yEDGE = 387,                   /* "edge"  */
    yELSE = 388,                   /* "else"  */
    yEND = 389,                    /* "end"  */
    yENDCASE = 390,                /* "endcase"  */
    yENDCHECKER = 391,             /* "endchecker"  */
    yENDCLASS = 392,               /* "endclass"  */
    yENDCLOCKING = 393,            /* "endclocking"  */
    yENDCONFIG = 394,              /* "endconfig"  */
    yENDFUNCTION = 395,            /* "endfunction"  */
    yENDGENERATE = 396,            /* "endgenerate"  */
    yENDGROUP = 397,               /* "endgroup"  */
    yENDINTERFACE = 398,           /* "endinterface"  */
    yENDMODULE = 399,              /* "endmodule"  */
    yENDPACKAGE = 400,             /* "endpackage"  */
    yENDPRIMITIVE = 401,           /* "endprimitive"  */
    yENDPROGRAM = 402,             /* "endprogram"  */
    yENDPROPERTY = 403,            /* "endproperty"  */
    yENDSEQUENCE = 404,            /* "endsequence"  */
    yENDSPECIFY = 405,             /* "endspecify"  */
    yENDTABLE = 406,               /* "endtable"  */
    yENDTASK = 407,                /* "endtask"  */
    yENUM = 408,                   /* "enum"  */
    yEVENT = 409,                  /* "event"  */
    yEVENTUALLY = 410,             /* "eventually"  */
    yEXPECT = 411,                 /* "expect"  */
    yEXPORT = 412,                 /* "export"  */
    yEXTENDS = 413,                /* "extends"  */
    yEXTERN = 414,                 /* "extern"  */
    yFINAL = 415,                  /* "final"  */
    yFIRST_MATCH = 416,            /* "first_match"  */
    yFOR = 417,                    /* "for"  */
    yFORCE = 418,                  /* "force"  */
    yFOREACH = 419,                /* "foreach"  */
    yFOREVER = 420,                /* "forever"  */
    yFORK = 421,                   /* "fork"  */
    yFORKJOIN = 422,               /* "forkjoin"  */
    yFUNCTION = 423,               /* "function"  */
    yGENERATE = 424,               /* "generate"  */
    yGENVAR = 425,                 /* "genvar"  */
    yGLOBAL__CLOCKING = 426,       /* "global-then-clocking"  */
    yGLOBAL__ETC = 427,            /* "global"  */
    yGLOBAL__LEX = 428,            /* "global-in-lex"  */
    yHIGHZ0 = 429,                 /* "highz0"  */
    yHIGHZ1 = 430,                 /* "highz1"  */
    yIF = 431,                     /* "if"  */
    yIFF = 432,                    /* "iff"  */
    yIGNORE_BINS = 433,            /* "ignore_bins"  */
    yILLEGAL_BINS = 434,           /* "illegal_bins"  */
    yIMPLEMENTS = 435,             /* "implements"  */
    yIMPLIES = 436,                /* "implies"  */
    yIMPORT = 437,                 /* "import"  */
    yINCDIR = 438,                 /* "incdir"  */
    yINCLUDE = 439,                /* "include"  */
    yINITIAL = 440,                /* "initial"  */
    yINOUT = 441,                  /* "inout"  */
    yINPUT = 442,                  /* "input"  */
    yINSIDE = 443,                 /* "inside"  */
    yINSTANCE = 444,               /* "instance"  */
    yINT = 445,                    /* "int"  */
    yINTEGER = 446,                /* "integer"  */
    yINTERCONNECT = 447,           /* "interconnect"  */
    yINTERFACE = 448,              /* "interface"  */
    yINTERSECT = 449,              /* "intersect"  */
    yJOIN = 450,                   /* "join"  */
    yJOIN_ANY = 451,               /* "join_any"  */
    yJOIN_NONE = 452,              /* "join_none"  */
    yLET = 453,                    /* "let"  */
    yLIBLIST = 454,                /* "liblist"  */
    yLIBRARY = 455,                /* "library"  */
    yLOCALPARAM = 456,             /* "localparam"  */
    yLOCAL__COLONCOLON = 457,      /* "local-then-::"  */
    yLOCAL__ETC = 458,             /* "local"  */
    yLOCAL__LEX = 459,             /* "local-in-lex"  */
    yLOGIC = 460,                  /* "logic"  */
    yLONGINT = 461,                /* "longint"  */
    yMATCHES = 462,                /* "matches"  */
    yMODPORT = 463,                /* "modport"  */
    yMODULE = 464,                 /* "module"  */
    yNAND = 465,                   /* "nand"  */
    yNEGEDGE = 466,                /* "negedge"  */
    yNETTYPE = 467,                /* "nettype"  */
    yNEW__ETC = 468,               /* "new"  */
    yNEW__LEX = 469,               /* "new-in-lex"  */
    yNEW__PAREN = 470,             /* "new-then-paren"  */
    yNEXTTIME = 471,               /* "nexttime"  */
    yNMOS = 472,                   /* "nmos"  */
    yNOR = 473,                    /* "nor"  */
    yNOT = 474,                    /* "not"  */
    yNOTIF0 = 475,                 /* "notif0"  */
    yNOTIF1 = 476,                 /* "notif1"  */
    yNULL = 477,                   /* "null"  */
    yOR = 478,                     /* "or"  */
    yOUTPUT = 479,                 /* "output"  */
    yPACKAGE = 480,                /* "package"  */
    yPACKED = 481,                 /* "packed"  */
    yPARAMETER = 482,              /* "parameter"  */
    yPMOS = 483,                   /* "pmos"  */
    yPOSEDGE = 484,                /* "posedge"  */
    yPRIMITIVE = 485,              /* "primitive"  */
    yPRIORITY = 486,               /* "priority"  */
    yPROGRAM = 487,                /* "program"  */
    yPROPERTY = 488,               /* "property"  */
    yPROTECTED = 489,              /* "protected"  */
    yPULL0 = 490,                  /* "pull0"  */
    yPULL1 = 491,                  /* "pull1"  */
    yPULLDOWN = 492,               /* "pulldown"  */
    yPULLUP = 493,                 /* "pullup"  */
    yPURE = 494,                   /* "pure"  */
    yRAND = 495,                   /* "rand"  */
    yRANDC = 496,                  /* "randc"  */
    yRANDCASE = 497,               /* "randcase"  */
    yRANDOMIZE = 498,              /* "randomize"  */
    yRANDSEQUENCE = 499,           /* "randsequence"  */
    yRCMOS = 500,                  /* "rcmos"  */
    yREAL = 501,                   /* "real"  */
    yREALTIME = 502,               /* "realtime"  */
    yREF = 503,                    /* "ref"  */
    yREG = 504,                    /* "reg"  */
    yREJECT_ON = 505,              /* "reject_on"  */
    yRELEASE = 506,                /* "release"  */
    yREPEAT = 507,                 /* "repeat"  */
    yRESTRICT = 508,               /* "restrict"  */
    yRETURN = 509,                 /* "return"  */
    yRNMOS = 510,                  /* "rnmos"  */
    yRPMOS = 511,                  /* "rpmos"  */
    yRTRAN = 512,                  /* "rtran"  */
    yRTRANIF0 = 513,               /* "rtranif0"  */
    yRTRANIF1 = 514,               /* "rtranif1"  */
    ySCALARED = 515,               /* "scalared"  */
    ySEQUENCE = 516,               /* "sequence"  */
    ySHORTINT = 517,               /* "shortint"  */
    ySHORTREAL = 518,              /* "shortreal"  */
    ySIGNED = 519,                 /* "signed"  */
    ySOFT = 520,                   /* "soft"  */
    ySOLVE = 521,                  /* "solve"  */
    ySPECIFY = 522,                /* "specify"  */
    ySPECPARAM = 523,              /* "specparam"  */
    ySTATIC__CONSTRAINT = 524,     /* "static-then-constraint"  */
    ySTATIC__ETC = 525,            /* "static"  */
    ySTATIC__LEX = 526,            /* "static-in-lex"  */
    ySTRING = 527,                 /* "string"  */
    ySTRONG = 528,                 /* "strong"  */
    ySTRONG0 = 529,                /* "strong0"  */
    ySTRONG1 = 530,                /* "strong1"  */
    ySTRUCT = 531,                 /* "struct"  */
    ySUPER = 532,                  /* "super"  */
    ySUPPLY0 = 533,                /* "supply0"  */
    ySUPPLY1 = 534,                /* "supply1"  */
    ySYNC_ACCEPT_ON = 535,         /* "sync_accept_on"  */
    ySYNC_REJECT_ON = 536,         /* "sync_reject_on"  */
    yS_ALWAYS = 537,               /* "s_always"  */
    yS_EVENTUALLY = 538,           /* "s_eventually"  */
    yS_NEXTTIME = 539,             /* "s_nexttime"  */
    yS_UNTIL = 540,                /* "s_until"  */
    yS_UNTIL_WITH = 541,           /* "s_until_with"  */
    yTABLE = 542,                  /* "table"  */
    yTAGGED = 543,                 /* "tagged"  */
    yTASK = 544,                   /* "task"  */
    yTHIS = 545,                   /* "this"  */
    yTHROUGHOUT = 546,             /* "throughout"  */
    yTIME = 547,                   /* "time"  */
    yTIMEPRECISION = 548,          /* "timeprecision"  */
    yTIMEUNIT = 549,               /* "timeunit"  */
    yTRAN = 550,                   /* "tran"  */
    yTRANIF0 = 551,                /* "tranif0"  */
    yTRANIF1 = 552,                /* "tranif1"  */
    yTRI = 553,                    /* "tri"  */
    yTRI0 = 554,                   /* "tri0"  */
    yTRI1 = 555,                   /* "tri1"  */
    yTRIAND = 556,                 /* "triand"  */
    yTRIOR = 557,                  /* "trior"  */
    yTRIREG = 558,                 /* "trireg"  */
    yTRUE = 559,                   /* "true"  */
    yTYPEDEF = 560,                /* "typedef"  */
    yTYPE__EQ = 561,               /* "type-then-eqneq"  */
    yTYPE__ETC = 562,              /* "type"  */
    yTYPE__LEX = 563,              /* "type-in-lex"  */
    yUNION = 564,                  /* "union"  */
    yUNIQUE = 565,                 /* "unique"  */
    yUNIQUE0 = 566,                /* "unique0"  */
    yUNSIGNED = 567,               /* "unsigned"  */
    yUNTIL = 568,                  /* "until"  */
    yUNTIL_WITH = 569,             /* "until_with"  */
    yUNTYPED = 570,                /* "untyped"  */
    yUSE = 571,                    /* "use"  */
    yVAR = 572,                    /* "var"  */
    yVECTORED = 573,               /* "vectored"  */
    yVIRTUAL__CLASS = 574,         /* "virtual-then-class"  */
    yVIRTUAL__ETC = 575,           /* "virtual"  */
    yVIRTUAL__INTERFACE = 576,     /* "virtual-then-interface"  */
    yVIRTUAL__LEX = 577,           /* "virtual-in-lex"  */
    yVIRTUAL__anyID = 578,         /* "virtual-then-identifier"  */
    yVOID = 579,                   /* "void"  */
    yWAIT = 580,                   /* "wait"  */
    yWAIT_ORDER = 581,             /* "wait_order"  */
    yWAND = 582,                   /* "wand"  */
    yWEAK = 583,                   /* "weak"  */
    yWEAK0 = 584,                  /* "weak0"  */
    yWEAK1 = 585,                  /* "weak1"  */
    yWHILE = 586,                  /* "while"  */
    yWILDCARD = 587,               /* "wildcard"  */
    yWIRE = 588,                   /* "wire"  */
    yWITHIN = 589,                 /* "within"  */
    yWITH__BRA = 590,              /* "with-then-["  */
    yWITH__CUR = 591,              /* "with-then-{"  */
    yWITH__ETC = 592,              /* "with"  */
    yWITH__LEX = 593,              /* "with-in-lex"  */
    yWITH__PAREN = 594,            /* "with-then-("  */
    yWITH__PAREN_CUR = 595,        /* "with-then-(-then-{"  */
    yWOR = 596,                    /* "wor"  */
    yWREAL = 597,                  /* "wreal"  */
    yXNOR = 598,                   /* "xnor"  */
    yXOR = 599,                    /* "xor"  */
    yD_ACOS = 600,                 /* "$acos"  */
    yD_ACOSH = 601,                /* "$acosh"  */
    yD_ASIN = 602,                 /* "$asin"  */
    yD_ASINH = 603,                /* "$asinh"  */
    yD_ASSERTCTL = 604,            /* "$assertcontrol"  */
    yD_ASSERTFAILOFF = 605,        /* "$assertfailoff"  */
    yD_ASSERTFAILON = 606,         /* "$assertfailon"  */
    yD_ASSERTKILL = 607,           /* "$assertkill"  */
    yD_ASSERTNONVACUOUSON = 608,   /* "$assertnonvacuouson"  */
    yD_ASSERTOFF = 609,            /* "$assertoff"  */
    yD_ASSERTON = 610,             /* "$asserton"  */
    yD_ASSERTPASSOFF = 611,        /* "$assertpassoff"  */
    yD_ASSERTPASSON = 612,         /* "$assertpasson"  */
    yD_ASSERTVACUOUSOFF = 613,     /* "$assertvacuousoff"  */
    yD_ATAN = 614,                 /* "$atan"  */
    yD_ATAN2 = 615,                /* "$atan2"  */
    yD_ATANH = 616,                /* "$atanh"  */
    yD_BITS = 617,                 /* "$bits"  */
    yD_BITSTOREAL = 618,           /* "$bitstoreal"  */
    yD_BITSTOSHORTREAL = 619,      /* "$bitstoshortreal"  */
    yD_C = 620,                    /* "$c"  */
    yD_CPURE = 621,                /* "$cpure"  */
    yD_CAST = 622,                 /* "$cast"  */
    yD_CEIL = 623,                 /* "$ceil"  */
    yD_CHANGED = 624,              /* "$changed"  */
    yD_CHANGED_GCLK = 625,         /* "$changed_gclk"  */
    yD_CHANGING_GCLK = 626,        /* "$changing_gclk"  */
    yD_CLOG2 = 627,                /* "$clog2"  */
    yD_COS = 628,                  /* "$cos"  */
    yD_COSH = 629,                 /* "$cosh"  */
    yD_COUNTBITS = 630,            /* "$countbits"  */
    yD_COUNTONES = 631,            /* "$countones"  */
    yD_DIMENSIONS = 632,           /* "$dimensions"  */
    yD_DISPLAY = 633,              /* "$display"  */
    yD_DISPLAYB = 634,             /* "$displayb"  */
    yD_DISPLAYH = 635,             /* "$displayh"  */
    yD_DISPLAYO = 636,             /* "$displayo"  */
    yD_DIST_CHI_SQUARE = 637,      /* "$dist_chi_square"  */
    yD_DIST_ERLANG = 638,          /* "$dist_erlang"  */
    yD_DIST_EXPONENTIAL = 639,     /* "$dist_exponential"  */
    yD_DIST_NORMAL = 640,          /* "$dist_normal"  */
    yD_DIST_POISSON = 641,         /* "$dist_poisson"  */
    yD_DIST_T = 642,               /* "$dist_t"  */
    yD_DIST_UNIFORM = 643,         /* "$dist_uniform"  */
    yD_DUMPALL = 644,              /* "$dumpall"  */
    yD_DUMPFILE = 645,             /* "$dumpfile"  */
    yD_DUMPFLUSH = 646,            /* "$dumpflush"  */
    yD_DUMPLIMIT = 647,            /* "$dumplimit"  */
    yD_DUMPOFF = 648,              /* "$dumpoff"  */
    yD_DUMPON = 649,               /* "$dumpon"  */
    yD_DUMPPORTS = 650,            /* "$dumpports"  */
    yD_DUMPVARS = 651,             /* "$dumpvars"  */
    yD_ERROR = 652,                /* "$error"  */
    yD_EXIT = 653,                 /* "$exit"  */
    yD_EXP = 654,                  /* "$exp"  */
    yD_FALLING_GCLK = 655,         /* "$falling_gclk"  */
    yD_FATAL = 656,                /* "$fatal"  */
    yD_FCLOSE = 657,               /* "$fclose"  */
    yD_FDISPLAY = 658,             /* "$fdisplay"  */
    yD_FDISPLAYB = 659,            /* "$fdisplayb"  */
    yD_FDISPLAYH = 660,            /* "$fdisplayh"  */
    yD_FDISPLAYO = 661,            /* "$fdisplayo"  */
    yD_FELL = 662,                 /* "$fell"  */
    yD_FELL_GCLK = 663,            /* "$fell_gclk"  */
    yD_FEOF = 664,                 /* "$feof"  */
    yD_FERROR = 665,               /* "$ferror"  */
    yD_FFLUSH = 666,               /* "$fflush"  */
    yD_FGETC = 667,                /* "$fgetc"  */
    yD_FGETS = 668,                /* "$fgets"  */
    yD_FINISH = 669,               /* "$finish"  */
    yD_FLOOR = 670,                /* "$floor"  */
    yD_FMONITOR = 671,             /* "$fmonitor"  */
    yD_FMONITORB = 672,            /* "$fmonitorb"  */
    yD_FMONITORH = 673,            /* "$fmonitorh"  */
    yD_FMONITORO = 674,            /* "$fmonitoro"  */
    yD_FOPEN = 675,                /* "$fopen"  */
    yD_FREAD = 676,                /* "$fread"  */
    yD_FREWIND = 677,              /* "$frewind"  */
    yD_FSCANF = 678,               /* "$fscanf"  */
    yD_FSEEK = 679,                /* "$fseek"  */
    yD_FSTROBE = 680,              /* "$fstrobe"  */
    yD_FSTROBEB = 681,             /* "$fstrobeb"  */
    yD_FSTROBEH = 682,             /* "$fstrobeh"  */
    yD_FSTROBEO = 683,             /* "$fstrobeo"  */
    yD_FTELL = 684,                /* "$ftell"  */
    yD_FUTURE_GCLK = 685,          /* "$future_gclk"  */
    yD_FWRITE = 686,               /* "$fwrite"  */
    yD_FWRITEB = 687,              /* "$fwriteb"  */
    yD_FWRITEH = 688,              /* "$fwriteh"  */
    yD_FWRITEO = 689,              /* "$fwriteo"  */
    yD_GLOBAL_CLOCK = 690,         /* "$global_clock"  */
    yD_HIGH = 691,                 /* "$high"  */
    yD_HYPOT = 692,                /* "$hypot"  */
    yD_INCREMENT = 693,            /* "$increment"  */
    yD_INFERRED_DISABLE = 694,     /* "$inferred_disable"  */
    yD_INFO = 695,                 /* "$info"  */
    yD_ISUNBOUNDED = 696,          /* "$isunbounded"  */
    yD_ISUNKNOWN = 697,            /* "$isunknown"  */
    yD_ITOR = 698,                 /* "$itor"  */
    yD_LEFT = 699,                 /* "$left"  */
    yD_LN = 700,                   /* "$ln"  */
    yD_LOG10 = 701,                /* "$log10"  */
    yD_LOW = 702,                  /* "$low"  */
    yD_MONITOR = 703,              /* "$monitor"  */
    yD_MONITORB = 704,             /* "$monitorb"  */
    yD_MONITORH = 705,             /* "$monitorh"  */
    yD_MONITORO = 706,             /* "$monitoro"  */
    yD_MONITOROFF = 707,           /* "$monitoroff"  */
    yD_MONITORON = 708,            /* "$monitoron"  */
    yD_ONEHOT = 709,               /* "$onehot"  */
    yD_ONEHOT0 = 710,              /* "$onehot0"  */
    yD_PAST = 711,                 /* "$past"  */
    yD_PAST_GCLK = 712,            /* "$past_gclk"  */
    yD_POW = 713,                  /* "$pow"  */
    yD_PRINTTIMESCALE = 714,       /* "$printtimescale"  */
    yD_RANDOM = 715,               /* "$random"  */
    yD_READMEMB = 716,             /* "$readmemb"  */
    yD_READMEMH = 717,             /* "$readmemh"  */
    yD_REALTIME = 718,             /* "$realtime"  */
    yD_REALTOBITS = 719,           /* "$realtobits"  */
    yD_REWIND = 720,               /* "$rewind"  */
    yD_RIGHT = 721,                /* "$right"  */
    yD_RISING_GCLK = 722,          /* "$rising_gclk"  */
    yD_ROOT = 723,                 /* "$root"  */
    yD_ROSE = 724,                 /* "$rose"  */
    yD_ROSE_GCLK = 725,            /* "$rose_gclk"  */
    yD_RTOI = 726,                 /* "$rtoi"  */
    yD_SAMPLED = 727,              /* "$sampled"  */
    yD_SDF_ANNOTATE = 728,         /* "$sdf_annotate"  */
    yD_SETUPHOLD = 729,            /* "$setuphold"  */
    yD_SFORMAT = 730,              /* "$sformat"  */
    yD_SFORMATF = 731,             /* "$sformatf"  */
    yD_SHORTREALTOBITS = 732,      /* "$shortrealtobits"  */
    yD_SIGNED = 733,               /* "$signed"  */
    yD_SIN = 734,                  /* "$sin"  */
    yD_SINH = 735,                 /* "$sinh"  */
    yD_SIZE = 736,                 /* "$size"  */
    yD_SQRT = 737,                 /* "$sqrt"  */
    yD_SSCANF = 738,               /* "$sscanf"  */
    yD_STABLE = 739,               /* "$stable"  */
    yD_STABLE_GCLK = 740,          /* "$stable_gclk"  */
    yD_STACKTRACE = 741,           /* "$stacktrace"  */
    yD_STEADY_GCLK = 742,          /* "$steady_gclk"  */
    yD_STIME = 743,                /* "$stime"  */
    yD_STOP = 744,                 /* "$stop"  */
    yD_STROBE = 745,               /* "$strobe"  */
    yD_STROBEB = 746,              /* "$strobeb"  */
    yD_STROBEH = 747,              /* "$strobeh"  */
    yD_STROBEO = 748,              /* "$strobeo"  */
    yD_SWRITE = 749,               /* "$swrite"  */
    yD_SWRITEB = 750,              /* "$swriteb"  */
    yD_SWRITEH = 751,              /* "$swriteh"  */
    yD_SWRITEO = 752,              /* "$swriteo"  */
    yD_SYSTEM = 753,               /* "$system"  */
    yD_TAN = 754,                  /* "$tan"  */
    yD_TANH = 755,                 /* "$tanh"  */
    yD_TESTPLUSARGS = 756,         /* "$test$plusargs"  */
    yD_TIME = 757,                 /* "$time"  */
    yD_TIMEFORMAT = 758,           /* "$timeformat"  */
    yD_TIMEPRECISION = 759,        /* "$timeprecision"  */
    yD_TIMEUNIT = 760,             /* "$timeunit"  */
    yD_TYPENAME = 761,             /* "$typename"  */
    yD_UNGETC = 762,               /* "$ungetc"  */
    yD_UNIT = 763,                 /* "$unit"  */
    yD_UNPACKED_DIMENSIONS = 764,  /* "$unpacked_dimensions"  */
    yD_UNSIGNED = 765,             /* "$unsigned"  */
    yD_URANDOM = 766,              /* "$urandom"  */
    yD_URANDOM_RANGE = 767,        /* "$urandom_range"  */
    yD_VALUEPLUSARGS = 768,        /* "$value$plusargs"  */
    yD_WARNING = 769,              /* "$warning"  */
    yD_WRITE = 770,                /* "$write"  */
    yD_WRITEB = 771,               /* "$writeb"  */
    yD_WRITEH = 772,               /* "$writeh"  */
    yD_WRITEMEMB = 773,            /* "$writememb"  */
    yD_WRITEMEMH = 774,            /* "$writememh"  */
    yD_WRITEO = 775,               /* "$writeo"  */
    yVL_CLOCKER = 776,             /* "/\*verilator clocker*\/"  */
    yVL_CLOCK_ENABLE = 777,        /* "/\*verilator clock_enable*\/"  */
    yVL_COVERAGE_BLOCK_OFF = 778,  /* "/\*verilator coverage_block_off*\/"  */
    yVL_FORCEABLE = 779,           /* "/\*verilator forceable*\/"  */
    yVL_FULL_CASE = 780,           /* "/\*verilator full_case*\/"  */
    yVL_HIER_BLOCK = 781,          /* "/\*verilator hier_block*\/"  */
    yVL_INLINE_MODULE = 782,       /* "/\*verilator inline_module*\/"  */
    yVL_ISOLATE_ASSIGNMENTS = 783, /* "/\*verilator isolate_assignments*\/"  */
    yVL_NO_CLOCKER = 784,          /* "/\*verilator no_clocker*\/"  */
    yVL_NO_INLINE_MODULE = 785,    /* "/\*verilator no_inline_module*\/"  */
    yVL_NO_INLINE_TASK = 786,      /* "/\*verilator no_inline_task*\/"  */
    yVL_PARALLEL_CASE = 787,       /* "/\*verilator parallel_case*\/"  */
    yVL_PUBLIC = 788,              /* "/\*verilator public*\/"  */
    yVL_PUBLIC_FLAT = 789,         /* "/\*verilator public_flat*\/"  */
    yVL_PUBLIC_FLAT_ON = 790,      /* "/\*verilator public_flat_on*\/"  */
    yVL_PUBLIC_FLAT_RD = 791,      /* "/\*verilator public_flat_rd*\/"  */
    yVL_PUBLIC_FLAT_RD_ON = 792,   /* "/\*verilator public_flat_rd_on*\/"  */
    yVL_PUBLIC_FLAT_RW = 793,      /* "/\*verilator public_flat_rw*\/"  */
    yVL_PUBLIC_FLAT_RW_ON = 794,   /* "/\*verilator public_flat_rw_on*\/"  */
    yVL_PUBLIC_FLAT_RW_ON_SNS = 795, /* "/\*verilator public_flat_rw_on_sns*\/"  */
    yVL_PUBLIC_ON = 796,           /* "/\*verilator public_on*\/"  */
    yVL_PUBLIC_OFF = 797,          /* "/\*verilator public_off*\/"  */
    yVL_PUBLIC_MODULE = 798,       /* "/\*verilator public_module*\/"  */
    yVL_SC_BIGUINT = 799,          /* "/\*verilator sc_biguint*\/"  */
    yVL_SC_BV = 800,               /* "/\*verilator sc_bv*\/"  */
    yVL_SFORMAT = 801,             /* "/\*verilator sformat*\/"  */
    yVL_SPLIT_VAR = 802,           /* "/\*verilator split_var*\/"  */
    yVL_TAG = 803,                 /* "/\*verilator tag*\/"  */
    yVL_UNROLL_DISABLE = 804,      /* "/\*verilator unroll_disable*\/"  */
    yVL_UNROLL_FULL = 805,         /* "/\*verilator unroll_full*\/"  */
    yP_TICK = 806,                 /* "'"  */
    yP_TICKBRA = 807,              /* "'{"  */
    yP_OROR = 808,                 /* "||"  */
    yP_ANDAND = 809,               /* "&&"  */
    yP_NOR = 810,                  /* "~|"  */
    yP_XNOR = 811,                 /* "^~"  */
    yP_NAND = 812,                 /* "~&"  */
    yP_EQUAL = 813,                /* "=="  */
    yP_NOTEQUAL = 814,             /* "!="  */
    yP_CASEEQUAL = 815,            /* "==="  */
    yP_CASENOTEQUAL = 816,         /* "!=="  */
    yP_WILDEQUAL = 817,            /* "==?"  */
    yP_WILDNOTEQUAL = 818,         /* "!=?"  */
    yP_GTE = 819,                  /* ">="  */
    yP_LTE = 820,                  /* "<="  */
    yP_LTE__IGNORE = 821,          /* "<=-ignored"  */
    yP_SLEFT = 822,                /* "<<"  */
    yP_SRIGHT = 823,               /* ">>"  */
    yP_SSRIGHT = 824,              /* ">>>"  */
    yP_POW = 825,                  /* "**"  */
    yP_COLON__BEGIN = 826,         /* ":-then-begin"  */
    yP_COLON__FORK = 827,          /* ":-then-fork"  */
    yP_EQ__NEW = 828,              /* "=-then-new"  */
    yP_PAR__IGNORE = 829,          /* "(-ignored"  */
    yP_PAR__STRENGTH = 830,        /* "(-for-strength"  */
    yP_LTMINUSGT = 831,            /* "<->"  */
    yP_PLUSCOLON = 832,            /* "+:"  */
    yP_MINUSCOLON = 833,           /* "-:"  */
    yP_MINUSGT = 834,              /* "->"  */
    yP_MINUSGTGT = 835,            /* "->>"  */
    yP_EQGT = 836,                 /* "=>"  */
    yP_ASTGT = 837,                /* "*>"  */
    yP_ANDANDAND = 838,            /* "&&&"  */
    yP_POUNDPOUND = 839,           /* "##"  */
    yP_POUNDMINUSPD = 840,         /* "#-#"  */
    yP_POUNDEQPD = 841,            /* "#=#"  */
    yP_DOTSTAR = 842,              /* ".*"  */
    yP_ATAT = 843,                 /* "@@"  */
    yP_COLONCOLON = 844,           /* "::"  */
    yP_COLONEQ = 845,              /* ":="  */
    yP_COLONDIV = 846,             /* ":/"  */
    yP_ORMINUSGT = 847,            /* "|->"  */
    yP_OREQGT = 848,               /* "|=>"  */
    yP_BRASTAR = 849,              /* "[*"  */
    yP_BRAEQ = 850,                /* "[="  */
    yP_BRAMINUSGT = 851,           /* "[->"  */
    yP_BRAPLUSKET = 852,           /* "[+]"  */
    yP_PLUSPLUS = 853,             /* "++"  */
    yP_MINUSMINUS = 854,           /* "--"  */
    yP_PLUSEQ = 855,               /* "+="  */
    yP_MINUSEQ = 856,              /* "-="  */
    yP_TIMESEQ = 857,              /* "*="  */
    yP_DIVEQ = 858,                /* "/="  */
    yP_MODEQ = 859,                /* "%="  */
    yP_ANDEQ = 860,                /* "&="  */
    yP_OREQ = 861,                 /* "|="  */
    yP_XOREQ = 862,                /* "^="  */
    yP_SLEFTEQ = 863,              /* "<<="  */
    yP_SRIGHTEQ = 864,             /* ">>="  */
    yP_SSRIGHTEQ = 865,            /* ">>>="  */
    yP_PLUSSLASHMINUS = 866,       /* "+/-"  */
    yP_PLUSPCTMINUS = 867,         /* "+%-"  */
    prTAGGED = 868,                /* prTAGGED  */
    prPOUNDPOUND_MULTI = 869,      /* prPOUNDPOUND_MULTI  */
    prUNARYARITH = 870,            /* prUNARYARITH  */
    prREDUCTION = 871,             /* prREDUCTION  */
    prNEGATION = 872,              /* prNEGATION  */
    prLOWER_THAN_ELSE = 873        /* prLOWER_THAN_ELSE  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */


extern YYSTYPE yylval;


int yyparse (void);


#endif /* !YY_YY_HOME_RUNNER_WORK_VERILATOR_VERILATOR_CODEQL_BUILD_DIR_SRC_V3PARSEBISON_PRETMP_H_INCLUDED  */
