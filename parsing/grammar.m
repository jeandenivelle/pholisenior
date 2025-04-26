%startsymbol File EOF

%symbol File
%symbol{} Statement Expr

%symbol{ logic::term } Term DotTerm ApplTerm EqTerm
%symbol{ logic::term } UnTermWith UnTermWithout
%symbol{ logic::term } AndTermWith AndTermWithout
%symbol{ logic::term } OrTermWith OrTermWithout
%symbol{ logic::term } ImpliesTermWith ImpliesTermWithout
%symbol{ logic::term } EquivTermWith EquivTermWithout

%symbol{ logic::term } GreedyPrefTerm
   // Greedy Prefix Term that grabs everything to the right.

%symbol{ std::vector< logic::term > } ArgSeq

%symbol{ logic::belief } struct_specifier
%symbol{std::stack<std::vector<std::pair<std::vector<std::string>, logic::type>>>} args_seq 
%symbol{ logic::type } StructType func 
%symbol{ std::vector< logic::type > } StructTypeSeq
%symbol{} iff_expr implication_expr not_expr quantifier_expr lazy_implication lazy_or lazy_and

%symbol{std::vector<std::pair<std::vector<std::string>, logic::type>>} idents_type_list 
%symbol{ std::string } VARIABLE
%symbol{ identifier } Identifier IdentifierStart

%symbol{ std::vector< std::string > } VarSeq
%symbol{ std::vector< logic::vartype > } VarTypeSeq VarsOneType 
   // VarsOneType has form v1, ..., vn : T 

%symbol{} STRUCT DEF FRM

%symbol{ } EOF FILEBAD WHITESPACE COMMENT 
%symbol{ } LPAR RPAR LBRACE RBRACE LBRACKET RBRACKET LEXISTS REXISTS
%symbol{ } EQ NE ASSIGN
%symbol{ } NOT PROP
%symbol{ } AND OR IMPLIES EQUIV 
%symbol{ } COLON SEMICOLON COMMA DOT SEP
%symbol{ } FALSE ERROR TRUE
%symbol{ } LET LAMBDA IN 
%symbol{ std::string } SCANERROR

%symbol{ } apply_expr member_apply_expr

%symbol{} iff_expr_q implication_expr_q not_expr_q

%symbolcode_h { #include "location.h" }
%symbolcode_h { #include <vector> }
%symbolcode_h { #include <string> }
%symbolcode_h { #include <stack> }
%symbolcode_h { #include "logic/type.h" }
%symbolcode_h { #include "./logic/selector.h" }
%symbolcode_h { #include "./identifier.h" }
%symbolcode_h { #include <typeinfo> }
%symbolcode_h { #include "./logic/belief.h"}
%symbolcode_h { #include "./logic/beliefstate.h"}

%symbolspace parsing
%parserspace parsing

%parsercode_h { #include "tokenizer.h" }
%parsercode_h { #include "logic/beliefstate.h" }

%infotype{ location }

%parameter { tokenizer }              tok
%parameter { logic::beliefstate }     blfs

%source{ tok. read( ); }

%rules 

//-------------------------common--------------------------------


File => 
    | File Term : tm SEMICOLON {
         std::cout << "the term = " << tm << "\n";
      }
         | File _recover_ SEMICOLON
         ;

Term => EquivTermWith : tm { return tm; }
;

// idents_type_list => VarTypeSeq : ict { return {ict}; }
// 		   | VarTypeSeq : ict COMMA idents_type_list:v 
// 				      { v.push_back(ict); return v; }
// 			      ;

VarSeq => VARIABLE : v 
{ 
   std::vector< std::string > res; 
   res. push_back(v); 
   return res; 
} 
| VarSeq : seq COMMA VARIABLE : v 
{
   seq. push_back(v);
   return std::move( seq );
}
;   

VarsOneType => VarSeq : seq COLON StructType : tp 
{
   std::vector< logic::vartype > res;
   for( const auto& v : seq )
      res. push_back( logic::vartype( v, tp ));
   return res; 
}
;

VarTypeSeq => VarsOneType : vot
{ 
   return std::move( vot ); 
}
| VarTypeSeq : seq COMMA VarsOneType : vot
{
   for( auto& v : vot )
      seq. push_back( std::move(v) );
   return std::move( seq ); 
}
;

StructType => 
   Identifier : id { return logic::type( logic::type_unchecked, id ); }
|
   StructType : f LPAR StructTypeSeq : tps RPAR 
   {
      return logic::type( logic::type_func, f, tps.begin( ), tps.end( ));
   }
; 

StructTypeSeq => StructType:t 
   { return std::vector< logic::type > {t}; }
| StructTypeSeq:v COMMA StructType : t 
   { v.push_back(t); return std::move(v); }
;

IdentifierStart => 
   { return identifier( ); }
|
   SEP 
   { return identifier( ) + ""; }
;

Identifier => IdentifierStart : id VARIABLE : v { return id + v; } 
           | Identifier : id SEP VARIABLE : v  { return id + v; } 
           ;


// -----------------------structs---------------------------------

struct_specifier => STRUCT VARIABLE:s ASSIGN idents_type_list:v  
{
	std::cout << "STRUCT!\n";

    logic::structdef strctseq;
    for (auto it = v.end(); it-- != v.begin(); ) {
    	for (auto jt = it -> first.end(); jt-- != it -> first.begin(); ) {
        	strctseq.append(identifier() + (*jt), it -> second);
       	}
    } 
    return logic::belief(logic::bel_struct, identifier() + s, strctseq);
}; 

//-----------------------defs---------------------------------

%skip 
def_specifier => DEF VARIABLE args_seq ASSIGN Term {std::cout << "Definition!\n";};		  

args_seq => args_seq:st LPAR idents_type_list:v RPAR {st.push(v); return st;}
		  | LPAR idents_type_list:v RPAR {
			  std::stack<std::vector<std::pair<std::vector<std::string>,
		      logic::type>>> st; st.push(v); return st;
		  }
		  | LPAR RPAR {
		      std::stack<std::vector<std::pair<std::vector<std::string>,
		  	  logic::type>>> st; return st;
		  };

%endskip

// These are these greedy prefix operators that eat everything
// that comes behind them:

GreedyPrefTerm => LBRACKET VarTypeSeq : vars RBRACKET Term : body
{
   return logic::term( logic::op_forall, body, vars. begin( ), vars. end( ));
}
| LEXISTS VarTypeSeq : vars REXISTS Term : body
{
   return logic::term( logic::op_exists, body, vars. begin( ), vars. end( ));
}
| LAMBDA VarTypeSeq : vars IN Term : body
{
   return logic::term( logic::op_lambda, body, vars. begin( ), vars. end( ));
}

| LBRACE Term : t1 RBRACE AND Term : t2 
{
   return logic::term( logic::op_lazy_and, t1, t2 );
}
| LBRACE Term : t1 RBRACE IMPLIES Term : t2
{
   return logic::term( logic::op_lazy_implies, t1, t2 );
}
| LBRACE Term : t1 RBRACE OR Term : t2
{
   return logic::term( logic::op_or, t1, t2 );
}
;


EquivTermWith => ImpliesTermWith : t { return std::move(t); }
|  ImpliesTermWithout : t1 EQUIV ImpliesTermWith : t2
{
   return logic::term( logic::op_equiv, t1, t2 );
};

EquivTermWithout => ImpliesTermWithout : t { return std::move(t); }
|  ImpliesTermWithout : t1 EQUIV ImpliesTermWithout : t2 
{
   return logic::term( logic::op_equiv, t1, t2 );
};


ImpliesTermWith => OrTermWith : t { return std::move(t); }
|
   OrTermWithout : t1 IMPLIES ImpliesTermWith : t2 
{
   return logic::term( logic::op_implies, t1, t2 );
}
;

ImpliesTermWithout => OrTermWithout : t { return std::move(t); }
|
   OrTermWithout : t1 IMPLIES ImpliesTermWithout : t2 
{
   return logic::term( logic::op_implies, t1, t2 );
}
;


OrTermWith => AndTermWith : t { return std::move(t); }
| OrTermWithout : t1 OR AndTermWith : t2 
      { return logic::term( logic::op_or, t1, t2 ); }
;

OrTermWithout => AndTermWithout : t { return std::move(t); }
| OrTermWithout : t1 OR AndTermWithout : t2 
      { return logic::term( logic::op_or, t1, t2 ); }
;


AndTermWith => UnTermWith : t { return std::move(t); }
| AndTermWithout : t1 AND UnTermWith : t2 
      { return logic::term( logic::op_and, t1, t2 ); }
;

AndTermWithout => UnTermWithout : t { return std::move(t); }
| AndTermWithout : t1 AND UnTermWithout : t2 
   { return logic::term( logic::op_and, t1, t2 ); }
;

UnTermWith =>
   EqTerm : t { return std::move(t); }
|
   NOT UnTermWith : t { return logic::term( logic::op_not, t ); }
|
   PROP UnTermWith : t { return logic::term( logic::op_prop, t ); }
|
   GreedyPrefTerm : gr { return std::move(gr); }    
;

UnTermWithout =>
   EqTerm : t { return std::move(t); }
|
   NOT UnTermWithout : t { return logic::term( logic::op_not, t ); }
|
   PROP UnTermWithout : t { return logic::term( logic::op_prop, t ); }
;

EqTerm =>
   DotTerm : t { return std::move( t ); }
|
   DotTerm : t1 EQ DotTerm : t2 
      { return logic::term( logic::op_equals, t1, t2 ); }

|
   DotTerm : t1 NE DotTerm : t2 
   { return logic::term( logic::op_not, 
               logic::term( logic::op_equals, t1, t2 ));
   }
;


DotTerm => 
   ApplTerm : tm { return std::move( tm ); } 
|
   DotTerm : first DOT Identifier : func
{
   logic::term tm = logic::term( logic::op_apply, 
                                 logic::term( logic::op_unchecked, func ),
                                 std::initializer_list< logic::term > ( ));
   auto fv = tm. view_apply( );
   fv. push_back( std::move( first )); 
   return tm;
}
| 
   DotTerm : first DOT Identifier : func LPAR ArgSeq : rest RPAR 
{
   logic::term tm = logic::term( logic::op_apply, 
                                 logic::term( logic::op_unchecked, func ),
                                 std::initializer_list< logic::term > ( ));
   auto fv = tm. view_apply( );
   fv. push_back( std::move( first ));
   for( auto& a : rest )
      fv. push_back( std::move(a) ); 
   return tm; 
}
;

ApplTerm =>  
   ApplTerm : func LPAR ArgSeq : args RPAR
      { return logic::term( logic::op_apply, 
                            func, args. begin( ), args. end( )); }

| Identifier : id  { return logic::term( logic::op_unchecked, id ); }
| LPAR Term : tm RPAR { return std::move(tm); } 
; 

ArgSeq => ArgSeq : args COMMA Term : t 
   { args. push_back( std::move(t)); return std::move( args ); } 
            | Term : t
   { std::vector< logic::term > res;
     res. push_back( std::move(t)); 
     return res;
   } 
            ;

%end
 
