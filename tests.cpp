
#include "tests.h"

#include "errorstack.h"

#include "logic/termoperators.h"
#include "logic/kbo.h"
#include "logic/structural.h"

#include "calc/proofterm.h"
#include "calc/proofchecking.h"
#include "calc/clausify.h"

#include "logic/replacements.h" 
#include "logic/pretty.h"

#include "semantics/interpretation.h"

#include "parsing/parser.h"

void tests::add_settheory( logic::beliefstate& blfs )
{
   using namespace logic;

   type O = type( logic::type_obj );
   type T = type( logic::type_form );

   type O2O = type( type_func, O, { O } );
   type O2T = type( type_func, T, { O } );

   logic::structdef setdef;
   setdef. append( fielddecl( identifier( ) + "setlike", 
                              type( type_func, T, { O2T } )));
   setdef. append( fielddecl( identifier( ) + "mat", 
                              type( type_func, O, { O2T } )));

   blfs. append( belief( bel_struct, identifier( ) + "Settheory", setdef ));

   auto typed = forall( {{ "P", O2T }}, 
      implies( apply( "strict"_unchecked, { 0_db } ), 
         prop( apply( "setlike"_unchecked, { 1_db, 0_db } )) ) );

   auto empty = 
      forall( {{ "P", O2T }},
         lazy_implies( apply( "strict"_unchecked, { 0_db } ),
               implies( 
                  forall( {{ "x", O }}, ! apply( 1_db, { 0_db } )),
                  apply( "setlike"_unchecked, { 1_db, 0_db } ))) );

   auto singleton =
      forall( {{ "P", O2T }},
         lazy_implies( apply( "strict"_unchecked, { 0_db } ),
            implies( exists( {{ "x", O }}, forall( {{ "x1", O }},
                implies( apply( 2_db, { 0_db } ), 0_db == 1_db ))),
                apply( "setlike"_unchecked, { 1_db, 0_db } ) )));
        
   auto setunion =
      forall( {{ "P1", O2T }, { "P2", O2T }, { "Q", O2T }},
         lazy_implies(
            apply( "strict"_unchecked, { 2_db } ) &&
            apply( "strict"_unchecked, { 1_db } ) &&
            apply( "strict"_unchecked, { 0_db } ),
            implies(
               apply( "setlike"_unchecked, { 3_db, 2_db } ) &&
               apply( "setlike"_unchecked, { 3_db, 1_db } ),
               implies(
                  forall( {{ "x", O }},
                     implies( apply( 1_db, { 0_db } ),
                              apply( 3_db, { 0_db } ) ||
                              apply( 2_db, { 0_db } ))),
                     apply( "setlike"_unchecked, { 3_db, 0_db } )))));

   auto repl = apply( "setlike"_unchecked, { 3_db, 0_db } );

   {
      auto f1 = forall( {{ "x", O }}, 
         implies( apply( 3_db, { 0_db } ), 
                  apply( "setlike"_unchecked, { 4_db, apply( 2_db, { 0_db } ) } )));

      auto f2 = forall( {{ "x", O }}, 
         implies( apply( 3_db, { 0_db } ), 
            apply( "setlike"_unchecked, { 4_db, apply( 2_db, { 0_db } ) } )));

      auto f3 = forall( {{ "y", O }},
         implies( apply( 1_db, { 0_db } ), 
            exists( {{ "x", O }}, 
               lazy_and( apply( 4_db, { 0_db } ), 
                         apply( 3_db, { 0_db, 1_db } ))) ));

      repl = implies( f3, repl );
      repl = implies( f2, repl );
      repl = implies( apply( "setlike"_unchecked, { 3_db, 2_db } ), repl );
      repl = lazy_implies( apply( "strict"_unchecked, { 0_db } ), repl );
      repl = lazy_implies( f1, repl );
      repl = lazy_implies( apply( "strict"_unchecked, { 2_db } ), repl );

      repl = forall( {{ "Q", O2T }}, repl );
      repl = forall( {{ "F", type( type_func, O2T, { O } ) }}, repl );
      repl = forall( {{ "P", O2T }}, repl );
   }

   auto ext = apply( "mat"_unchecked, { 2_db, 1_db } ) == 
                 apply( "mat"_unchecked, { 2_db, 0_db } );

   {
      auto eq = forall( {{ "x", O }}, 
         equiv( apply( 2_db, { 0_db } ),
                apply( 1_db, { 0_db } )) );
      ext = implies( eq, ext );
      ext = lazy_implies( apply( "strict"_unchecked, { 1_db } ) &&
                          apply( "strict"_unchecked, { 0_db } ), ext );
      ext = forall( {{ "P1", O2T }, { "P2", O2T }}, ext );
   }

   auto bij =  forall( {{ "x", O }}, equiv( apply( 2_db, { 0_db } ),
                                            apply( 1_db, { 0_db } )) );
   bij = implies( apply( "mat"_unchecked, { 2_db, 1_db } ) ==
                  apply( "mat"_unchecked, { 2_db, 0_db } ), bij );
   bij = implies( apply( "setlike"_unchecked, { 2_db, 1_db } ) &&
                  apply( "setlike"_unchecked, { 2_db, 0_db } ), bij );
   bij = lazy_implies( apply( "strict"_unchecked, { 1_db } ) &&
                       apply( "strict"_unchecked, { 0_db } ), bij ); 
   bij = forall( {{ "P1", O2T }, { "P2", O2T }}, bij ); 

   auto powset = exists( {{ "P1", O2T }}, apply( "strict"_unchecked, { 0_db } ) &&
      forall( {{ "x", O }}, implies( apply( 1_db, { 0_db } ), apply( 3_db, { 0_db } )) &&
          2_db == apply( "mat"_unchecked, { 5_db, 1_db } )));

   powset = forall( {{ "y", O }}, implies( apply( 1_db, { 0_db } ), powset ));

   powset = implies( powset, apply( "setlike"_unchecked, { 2_db, 0_db } ));
   powset = implies( apply( "setlike"_unchecked, { 2_db, 1_db } ) &&
                     apply( "setlike"_unchecked, { 2_db, 0_db } ), powset );
   powset = lazy_implies( apply( "strict"_unchecked, { 1_db } ), powset );
   powset = forall( {{ "P", O2T }, { "Q", O2T }}, powset );

   auto settheory = lambda( {{ "t", type( type_unchecked, identifier( ) + "Settheory" ) }}, 
      lazy_and( typed, empty && singleton && setunion && repl && ext && bij && powset ));

   blfs. append( belief( bel_def, identifier( ) + "settheory", settheory, 
                                     type( type_func, T, 
                                     { type( type_unchecked, 
                                             identifier( ) + "Settheory" ) } ) ));
}


void tests::add_proof( logic::beliefstate& blfs )
{
   using namespace logic;

   type O = type( logic::type_obj );
   type T = type( logic::type_form );

   type O2O = type( type_func, O, { O } );
   type O2T = type( type_func, T, { O } );

   type Seq = type( type_unchecked, identifier( ) + "Seq" );

   blfs. append( belief( bel_symbol, identifier( ) + "s1", Seq ));
   blfs. append( belief( bel_symbol, identifier( ) + "s2", Seq ));

   // We could create more Skolem constants.

   auto cls = term( op_kleene_and, { } );
   auto cl_view = cls. view_kleene( );

   cl_view. push_back( 
       term( op_apply, "gen"_unchecked, { "s1"_unchecked, 1_db } ));
   cl_view. push_back( 
       term( op_apply, "gen"_unchecked, { "s2"_unchecked, 0_db } ));

   cl_view. push_back( term( op_apply, "minhomrel"_unchecked, 
            { "s1"_unchecked, "s2"_unchecked, 1_db, 0_db } ));

   cl_view. push_back( apply( "alpha1"_unchecked, { 1_db, 0_db } ));
   cl_view. push_back( apply( "alpha2"_unchecked, { 1_db, 0_db } )); 

   cls = term( op_kleene_exists, cls, {{ "x", O }, { "y", O }} );

   std::cout << cls << "\n";
   throw std::runtime_error( "quitting" );

   blfs. append( belief( bel_axiom, identifier( ) + "initial", cls, { proof( ) } ));
#if 0
   cls = term( op_kleene_or, { } );
   cl_view = cls. view_kleeneprop( );
#endif
}

void tests::clausify( logic::beliefstate& blfs )
{
   std::cout << "testing clausify\n";

   using namespace logic;
   type O = type( logic::type_obj );
   type T = type( logic::type_form );
   type O2T = type( type_func, T, { O } );
   type O2O = type( type_func, O, { O } );

   type Seq = type( type_unchecked, identifier( ) + "Seq" );
   type X = type( type_unchecked, identifier( ) + "X" );

   if( true )
   {
      auto all1 =
         forall( { { "y", O }}, 
            apply( "p1"_unchecked, { 0_db, 1_db } ) ||
            apply( "q1"_unchecked, { 0_db, 1_db } ));

      auto all2 =
         forall( { { "z", O2O }},
            apply( "p2"_unchecked, { 1_db, 0_db } ) ||
            exists( {{ "t", T }}, 
               apply( "q2"_unchecked, { 2_db, 1_db, 0_db } )));

      auto form = exists( { { "x", T }},
            apply( "a"_unchecked, { 0_db } ) &&
            exists( {{ "u", T }}, apply( "b"_unchecked, { 0_db, 1_db } )) ||
            ( all1 && all2 ));

      form = prop( !form );
      form = calc::kleene_top( form, calc::pol_neg );

      {
         logic::context ctxt; 
         std::cout << "result = ";
         std::cout << form << "\n";

         // pretty::print( std::cout, blfs, ctxt, form );
      }

#if 0
      calc::disj_stack disj;
      disj. append( form, 0 );
      std::vector< logic::term > conj;

      logic::context ctxt;
      calc::distr( ctxt, disj, conj );
      std::cout << "result is \n";
      for( const auto& c : conj )
      {
         pretty::print( std::cout, blfs, ctxt, c ); 
         std::cout << "\n";
      }

      return; 
#endif
   }

   if( false ) 
   {
      std::cout << "testing ANF\n";
      auto f = logic::term( logic::op_kleene_or, {  0_db == 2_db, 1_db == 3_db } );

      f = logic::term( logic::op_kleene_exists, f, {{ "a", O }, { "b", T }} );
      f = logic::term( logic::op_kleene_forall, f, {{ "x", T }, { "y", O2O }} ); 
      std::cout << f << "\n";

      // f = calc::alt_conj(f);
      std::cout << "\n" << f << "\n";

      return; 
   }

   const auto& f = blfs. getformulas( identifier( ) + "just" );
   if( f. size( ) != 1 )
      throw std::runtime_error( "cannot continue" );

   auto ind = blfs. at( f[0] );

   logic::context ctxt;

 
}


void tests::pretty( const logic::beliefstate& blfs )
{
   using namespace logic;

   auto O = type( type_obj );
   auto T = type( type_form );

   auto N2T = type( type_func, T, { } );

   auto O2T = type( type_func, T, { O } );
   auto OO2T = type( type_func, T, { O, O } );
   auto OOO2T = type( type_func, T, { O, type( type_struct, exact(44)), O } );
 
   term tm = ( 0_db && 1_db ) || ( 0_db != 1_db );
   tm = term( op_and, "xxxx"_unchecked, tm ) && term( op_exact, exact(23) );

   tm = lambda( {{ "x1", OOO2T }, { "x2", O2T }, { "y1", O }, { "s", O }}, tm );
   tm = apply( tm, { term( op_exact, exact(21)), term( op_false ) } );

   tm = term( op_kleene_and, { tm, term( op_exact, exact(25)), 0_db } );
   tm = term( op_kleene_and, { 0_db, tm } );

   std::cout << "\n";
   std::cout << "pretty: ";
   std::cout << tm << "\n";
   std::cout << "\n\n"; 

   pretty::uniquenamestack un;
   pretty::print( std::cout, blfs, un, tm, {0,0} );

#if 0
   initial. push_back( exists( { "x", S },
                         logic::term( logic::sel_appl, "p"_ident, { 0_db } ) ||
                         logic::term( logic::sel_appl, "q"_ident, { 0_db } )));
   initial. push_back( ! exists( { "x", S },
                         logic::term( logic::sel_appl, "p"_ident, { 0_db } )));
   initial. push_back( ! exists( { "x", S },
                         logic::term( logic::sel_appl, "p"_ident, { 0_db } )));   
   for( auto& init: initial )
      init = logic::simplifications::topnorm( init );

   for( const auto& f : initial )
   {
      if( is_confl( tab. insert_initial(f)))
      {
         std::cout << "**** was a conflict\n";
      }
   }

   std::cout << tab << "\n";
   std::cout << tab. try_refute(0) << "\n";
#endif

}

#if 0
void tests::setsimplifications( )
{
   std::cout << "testing set simplifications\n";

   logic::simplifications::settheoretic set;
   std::cout << set << "\n"; 
   std::cout << "\n";
 
   auto S = logic::type( logic::sel_set );
   auto T = logic::type( logic::sel_truthval );
   auto B = logic::type( logic::sel_belief );

   auto a = "A"_ident; 
   auto b = "B"_ident;
   auto c = "C"_ident; 

   auto t = logic::term( logic::sel_appl, "T"_ident, { 0_db } );

   auto fx = logic::term( logic::sel_appl, "f"_ident, { 0_db } );
   auto Pfx = logic::term( logic::sel_appl, 
                      "P"_ident, { fx } );

   logic::term func = logic::term( logic::sel_lambda, Pfx, { { "x", S }} ); 

   logic::term fa = forall( { "x", S }, 0_db && 1_db ); 
   logic::term f = logic::term( logic::sel_in, "x"_ident, 
       logic::term( logic::sel_insert, "t"_ident, "rest"_ident ));

   for( unsigned int i = 0; i < 6; ++ i )
   {
      auto f1 = set(f,0);
      std::cout << f << " ==>  " << f1 << "   ";
      if( f. very_equal_to( f1 ))
         std::cout << "result is very equal\n";
      else
         std::cout << "\n";

      f = !f;
   }
}

void tests::kbo( )
{

   std::cout << "testing KBO\n";

   logic::type S = logic::type(logic::sel_set);
   logic::type T = logic::type(logic::sel_truthval);
   logic::type B = logic::type(logic::sel_belief);

   logic::term a = logic::term(logic::sel_ident, "a"_ident );
   logic::term b = logic::term(logic::sel_ident, "b"_ident );
   logic::term c = logic::term(logic::sel_ident, "c"_ident );

   logic::term not1 = logic::term(logic::sel_not, a);
   logic::term not2 = logic::term(logic::sel_not, b);
   logic::term not3 = logic::term(logic::sel_not, not1);

   logic::term and1 = logic::term(logic::op_and, a, b);
   logic::term and2 = logic::term(logic::op_and, b, c);
   logic::term and3 = logic::term(logic::op_and, and1, c);

   logic::term appl1 = logic::term(logic::sel_appl, logic::term(logic::op_and, 0_db, 1_db ), {a, b});
   logic::term appl2 = logic::term(logic::sel_appl, logic::term(logic::op_and, 0_db, 1_db ), {b, c});
   logic::term appl3 = logic::term(logic::sel_appl, logic::term(logic::op_and, logic::term(logic::sel_not, 1_db )), {a, b} );
   logic::term appl4 = logic::term(logic::sel_appl, logic::term(logic::op_and, 0_db, logic::term(logic::sel_or, 1_db, 1_db )), {a, b, c});
   
}

#endif

void tests::replacements( ) 
{

   using namespace logic;

   type O = type( logic::type_obj );
   type T = type( logic::type_form );
   
   type O2O = type( type_func, O, { O } );
   type O2T = type( type_func, T, { O } );
   
   type Seq = type( type_unchecked, identifier( ) + "Seq" );

   term simp = 4_db && 7_db;

   simp = term( op_implies, simp, "xxxx"_unchecked );

   simp = term( op_forall, simp, {{ "x", O }} );
   simp = term( op_exists, simp, {{ "y", T }} );

   simp = term( op_lambda, simp, { { "v0", O }, { "v1", T } } );

   std::cout << simp << "\n";

   lifter lift(3);
   std::cout << lift << "\n";

   bool change = false; 
   simp. printstate( std::cout ); 
   auto simped = topdown( lift, std::move(simp), 0, change );

   std::cout << "simped = " << simped << "\n";
   simped. printstate( std::cout );
   std::cout << "change = " << change << "\n";

   {
      // contextsubst:
#if 0
      logic::contextsubst subst;
      subst. extend(4);
      subst. append( 4_db );
      subst. append( 3_db );
      subst. append( 2_db );
      subst. extend(2);
      std::cout << subst << "\n";
   
      bool change = false;
      auto tm = 1_db && 2_db && 3_db && 4_db;
      std::cout << tm << "\n";
      tm. printstate( std::cout );
      auto tm2 = topdown( subst, std::move(tm), 0, change );
      std::cout << tm2 << "\n"; 
      tm2. printstate( std::cout );
#endif
   }

#if 0
   logic::equalitysystem eq( { { 0_db, 1_db } } ); 
   std::cout << eq << "\n"; 

   long unsigned int changes = 0;
   auto simp2 = topdown_sar( changes, eq, std::move(simp), 0 );

   std::cout << "simp2 = " << simp2 << "\n";
   std::cout << "changes = " << changes << "\n"; 
#endif

}


#if 0
void tests::add_simple( logic::beliefstate& bs )
{
   logic::type S = logic::type( logic::sel_set );
   logic::type T = logic::type( logic::sel_truthval );

   auto thm = forall( { "a", T }, 
      implies( 0_db, 0_db ));

   auto unf = logic::term( logic::sel_lambda, 
                  logic::term( logic::prf_unfinished ), 
                  { { "goal", logic::type( logic::sel_belief ) } } );

   auto b = logic::belief( logic::bel_thm, thm, unf ); 
   bs. add( identifier( ) + "simple", b ); 

   // a = b, b = c -> a = c :

   thm = forall( { "a", S },
            forall( { "b", S },
               forall( { "c", S },
                  implies( 2_db == 1_db && 1_db == 0_db, 2_db == 0_db ))));
   bs. add( identifier( ) + "trans", logic::belief( logic::bel_thm, thm, unf ));  

   // [a,b:T] ( a -> b ) -> [a,b:T] ( !b -> !a ) :

   thm = implies( 
            forall( { "a", T },
               forall( { "b", T }, 
                  implies( 1_db, 0_db ))),
            forall( { "a", T },
               forall( { "b", T },
                  implies( ! 0_db, ! 1_db ))) )
;
   bs. add( identifier( ) + "contrapos", logic::belief( logic::bel_thm, thm, unf ));

}


#endif

void tests::parser( logic::beliefstate& blfs ) {
   lexing::filereader inp( &std::cin, "std::cin" );

   parsing::tokenizer tok( std::move( inp ));
   parsing::parser prs( tok, blfs );  

   prs. debug = 0;
   prs. checkattrtypes = 0;

   auto res = prs. parse( parsing::sym_File, std::cout );

}

#if 0

void tests::betareduction( ) 
{
   logic::betareduction beta;
   std::cout << beta << "\n";

   auto S = logic::type( logic::sel_set );
   auto T = logic::type( logic::sel_truthval );
   auto B = logic::type( logic::sel_belief );
   auto S2S = logic::type( logic::sel_func, S, { S } );

   logic::term body =
      logic::term( logic::sel_appl, "+"_ident, { 0_db, 1_db } );
 
   logic::term lambda = 
      logic::term( logic::sel_lambda, body, { { "x", S }, { "y", S }} );

   logic::term appl = 
      logic::term( logic::sel_appl, lambda, { "first"_ident, "second"_ident } );

   std::cout << "appl = " << appl << "\n";

   std::cout << beta( appl, 0 ) << "\n";

   body = 0_db;
   body = logic::term( logic::sel_appl, 1_db, { body } );
   body = logic::term( logic::sel_appl, 2_db, { body } );
   auto comp = logic::term( logic::sel_lambda, body, { { "x", S } } );
   comp = logic::term( logic::sel_lambda, comp, { { "f", S2S }, { "g", S2S } } );

   std::cout << comp << "\n";

   auto succ = "succ"_ident;
   auto succ2 = logic::term( logic::sel_lambda, 
                   logic::term( logic::sel_appl, succ, { 0_db } ), { { "x", S }} );
   std::cout << "succ2 " << succ2 << "\n";

   auto pred = "pred"_ident;
   auto pred2 = logic::term( logic::sel_lambda, 
                   logic::term( logic::sel_appl, pred, { 0_db } ), { { "x", S }} );
   std::cout << "pred2 " << pred2 << "\n";

   appl = logic::term( logic::sel_appl, comp, { pred2, succ2 } );
   appl = logic::term( logic::sel_appl, appl, { "zero"_ident } );

   std::cout << appl << "\n"; 

   std::cout << normalize_sar( beta, appl ) << "\n";
}

#endif

void tests::proofchecking( logic::beliefstate& blfs, errorstack& err )
{
   auto id = identifier( ) + "find2";

   const auto& f = blfs. getformulas( id );
   std::cout << f. size( ) << "\n";
   if( f. size( ) != 1 )
      throw std::runtime_error( "cannot continue" );

   auto seq = calc::sequent( blfs, err );
   seq. push( "initial", ! prop( blfs. at( f. front( )). view_thm( ). frm( )));

   std::cout << seq << "\n";


   calc::proofterm prf = calc::proofterm( calc::prf_truthconst );
   auto res = eval( seq, prf, err ); 
   std::cout << "evaluation result in " << res << "\n";

   prf = calc::proofterm( calc::prf_ident, identifier( ) + "initial0001" );
   res = eval( seq, prf, err ); 

   std::cout << res << "\n";
#if 0
   pretty::print( std::cout, bel ); 
   check_everything( std::cout, bel );

   auto thm = bel. at( bel. find( identifier( ) + "trans" )). second. view_thm( ). form( );
   logic::proofeditor edit( &bel, bel. size( ), !thm );

   using namespace logic;
#if 0
   std::cout << edit << "\n";

   edit. apply_exists( 0_db, "a", "h0_" );
   edit. apply_exists( 0_db, "b", "h1_" );
   edit. apply_exists( 0_db, "c", "h2_" );

   edit. show( std::cout, { 
      logic::term( logic::prf_and1, logic::term( logic::prf_and1, 0_db )),
      logic::term( logic::prf_and2, 0_db ),
      logic::term( logic::prf_repl,
         logic::term( logic::prf_and1, logic::term( logic::prf_and1, 0_db )),
         logic::term( logic::prf_and2, 0_db )) } );

   edit. apply_abbreviate( logic::term( logic::prf_repl,
         logic::term( logic::prf_and1, logic::term( logic::prf_and1, 0_db )),
         logic::term( logic::prf_and2, 0_db )), "repl" );

   edit. show( std::cout, { logic::term( logic::prf_repl,
         logic::term( logic::prf_and2, logic::term( logic::prf_and1, 1_db )),
         0_db ) } );

   edit. apply_proof( logic::term( logic::prf_false,
      logic::term( logic::prf_repl,
         logic::term( logic::prf_and2, logic::term( logic::prf_and1, 1_db )),
         0_db )) ); 

   edit. show( std::cout, { } );

   thm = bel. at( bel. find( identifier( ) + "contrapos" )). second. view_thm( ). form( );
   edit = logic::proofeditor( &bel, bel. size( ), !thm );

   std::cout << edit << "\n";

   edit. apply_exists( term( prf_and2, 0_db ), "a" );
   edit. apply_exists( 0_db, "b" );

   edit. apply_disj( term( prf_inst,
                            term( prf_inst, term( prf_and1, 4_db ), 3_db ), 1_db ) );

   edit. show( std::cout, { term( prf_and2, 1_db ) } );

   // Unfinished Point.

   return;

   edit. apply_exists( logic::term( logic::prf_and2, 0_db ), "a" );
   edit. apply_exists( 0_db, "b" );

   edit. show( std::cout, { logic::term( logic::prf_inst,
                               logic::term( logic::prf_inst,
                                  logic::term( logic::prf_and1, 4_db ), 3_db ),
                                  1_db ) } );
  
   edit. apply_disj( logic::term( logic::prf_inst,
                               logic::term( logic::prf_inst,
                                  logic::term( logic::prf_and1, 4_db ), 3_db ),
                                  1_db ),
                     "h", "h" );

   edit. apply_proof( logic::term( logic::prf_contr,
      0_db, logic::term( logic::prf_and2, 1_db )) );
 
   edit. show( std::cout, {} );

   edit. setfocus(1);
   edit. show( std::cout, {} );

   edit. apply_proof( logic::term( logic::prf_contr,
      0_db, logic::term( logic::prf_and1, 1_db )) ); 

   edit. setfocus(0);

   edit = logic::proofeditor( &bel, bel. size( ), 
      !bel. at( bel. find( identifier( ) + "def" + "expand" )). second. view_thm_file( ). form( ));

   edit. setfocus(0);
   logic::position pos;
   pos. extend(0);
   pos. extend(0);
   pos. extend(0);
   pos. extend(1);
   edit. show( std::cout, { logic::term( logic::prf_exp, 0_db, identifier( ) + "pair", pos ) } );

#if 0
   auto b = edit. apply_exists( 0_db, "a", "b" );  
   if( !b ) std::cout << "EXISTS FAILED\n";
   std::cout << edit << "\n";

   //return;
   
   edit. show( std::cout, { } );
   if( !edit. apply_abbreviate( logic::term( logic::prf_and1, 0_db ), "and" )) std::cout << "ABBREVIATE FAILED\n";
   if( !edit. apply_abbreviate( logic::term( logic::prf_and2, 1_db ), "and" )) std::cout << "ABBREVIATE FAILED\n";
   edit. show( std::cout, { } );

   //return;

   if( !edit. apply_proof( logic::term( logic::prf_contr, 0_db, 1_db )))
      std::cout << "IMMEDIATE FAILED\n";

#endif 
#endif
#endif
}

#if 0

void tests::unification( )
{
   reso::subst s(4);
   std::cout << s << "\n";

}

void tests::prove_pluscom( )
{
   using namespace logic;
#if 0
   logic::beliefstate bel;
   add_addition( bel );

   pretty::print( std::cout, bel );
   check_everything( std::cout, bel );

   // [x:S, y:S] nat(x) -> nat(y) -> succ(X) + Y = succ( X + Y ).

   size_t ind = bel. find( identifier( ) + "plus" + "zero" + "rev" );
   if( ind >= bel. size( ))
   {
      std::cout << "did not find the theorem\n";
      return;
   }

   auto thm = bel. at( ind ). second. view_thm( ). form( );
   logic::proofeditor edit( &bel, ind, !thm );
   std::cout << edit << "\n";

   edit. show( std::cout, 
               { term( sel_ident, identifier( ) + "peano" + "induction" ) } );

   edit. apply_abbreviate( { {
      "ind_hyp", 
      term( prf_inst,  
      term( sel_ident, identifier( ) + "peano" + "induction" ),
                  term( sel_lambda, 
                     term( sel_appl, "plus"_ident, { "zero"_ident, 0_db } ) == 0_db, 
                     { { "x", type( sel_set ) }} )) }} );


   edit. show( std::cout, { } );

   edit. apply_disj( 0_db );


   edit. apply_abbreviate( { 
        { "ax_zero", term( prf_inst, term( sel_ident, identifier( ) + "plus" + "zero" ), 
                           "zero"_ident ) },
        { "nat_zero", term( sel_ident, identifier( ) + "peano" + "zero" ) } } );

    
   edit. apply_proof( term( prf_axiom, { 0_db, 1_db, 2_db } ));

   edit. setfocus(0);

   edit. show( std::cout, { } );

   
   edit. apply_disj( 0_db );

   edit. apply_exists( 0_db );

   edit. apply_abbreviate(  
      {
      { "type_zero", term( sel_ident, identifier( ) + "peano" + "zero" ) }, 

      { "ax_zero", term( prf_inst, term( sel_ident, identifier( ) + "plus" + "zero" ), 
                         "zero"_ident ) },
      { "ax_succ", term( prf_inst,
                      term( sel_ident, identifier( ) + "plus" + "succ" ),
                      "zero"_ident ) }} ); 


   edit. apply_disj( 0_db );

   edit. apply_proof( term( prf_axiom, { 0_db, 3_db } ));

   edit. setfocus(0);
 
   edit. apply_abbreviate( { { "inst", term( prf_inst, 0_db, 5_db ) }} );

   edit. apply_proof( term( prf_axiom, { 0_db, 5_db } ));

   edit. setfocus(0);

   edit. apply_proof( term( prf_axiom, { 0_db, 3_db } ));

   edit. show( std::cout, { } );

   edit. setfocus(0);

   // Pluscom. 

   return;

   edit. apply_proof( term( prf_axiom, { 0_db, 1_db, 2_db } ));
   // Unfinished Point 

   edit. setfocus(2);

   std::cout << edit. check. nr_unfinished( ) << "\n";

   edit. show( std::cout, { } );
#if 0

   // Current Focus

   edit. apply_disj( 0_db );
   edit. apply_disj( logic::term( logic::prf_inst,
                                  logic::term( logic::sel_ident, identifier( ) + "plus" + "zero" ),
                                  "zero"_ident ));

   edit. apply_proof( logic::term( logic::prf_contr,
                        logic::term( logic::sel_ident, identifier( ) + "peano" + "zero" ),
                        0_db ));
   edit. setfocus(0);
   edit. apply_proof( logic::term( logic::prf_contr, 0_db, 1_db ));
   edit. setfocus(0);
   edit. apply_disj( 0_db );

   edit. apply_exists( 0_db );

   edit. apply_disj( logic::term( logic::prf_inst,
                               logic::term( logic::sel_ident, identifier( ) + "plus" + "succ" ),
                               "zero"_ident ));
   edit. apply_proof( logic::term( logic::prf_contr,
                        logic::term( logic::sel_ident, identifier( ) + "peano" + "zero" ),
                        0_db ));

   edit. setfocus(0);
   edit. apply_disj( logic::term( logic::prf_inst, 0_db, 2_db ));
   
   edit. apply_proof( logic::term( logic::prf_contr,
                        logic::term( logic::sel_ident, identifier( ) + "peano" + "zero" ),
                        0_db ));

   edit. setfocus(0);
   
   edit. apply_abbreviate( logic::term( logic::prf_repl, 
      logic::term( logic::prf_repl, logic::term( logic::prf_and1,
         logic::term( logic::prf_and2, 2_db )), 0_db ), 2_db ) );

   edit. apply_proof( logic::term( logic::prf_false, logic::term( logic::prf_and2, logic::term( logic::prf_and2, 0_db ))) );

   edit. setfocus(0);

   edit. apply_exists( 3_db );
   
   edit. apply_abbreviate( logic::term( logic::prf_inst, 2_db, 1_db ));

   edit. apply_disj( 0_db );

   edit. apply_proof( logic::term( logic::prf_contr, 0_db, 
                         logic::term( logic::prf_and1, 2_db )));

   edit. setfocus(0);

   edit. apply_proof( logic::term( logic::prf_contr, 0_db,
                         logic::term( logic::prf_and2, 2_db )));

   edit. setfocus(0);
   
   // edit. show( std::cout, { } );

#if 1  // Start proof plus::succ:rev
   ind = bel. find( identifier( ) + "plus" + "succ" + "rev" );
   if( ind >= bel. size( ))
   {
      std::cout << "did not find the theorem\n";
      return;
   }

   thm = bel. at( ind ). second. view_thm( ). form( );
   edit = logic::proofeditor( &bel, ind, !thm );

   edit. apply_exists( 0_db ); 
   edit. apply_abbreviate( term( prf_and1, 0_db )); 

   auto inductionhypothesis = 
      implies( apply( "nat"_ident, 0_db ),
                      apply( "plus"_ident, apply( "succ"_ident, 1_db ), 0_db ) ==
                      apply( "succ"_ident, apply( "plus"_ident, 1_db, 0_db )) );
   
   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "peano" + "induction" ),
                                            term( sel_lambda, inductionhypothesis, 
                                               { { "y", type( sel_set ) }} ) + 2 ) );  
   
   edit. apply_disj( 0_db );

   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "plus" + "zero" ),
                                           4_db ) );
   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "plus" + "zero" ),
                                           term( sel_appl, "succ"_ident, { 5_db } )) );

   edit. apply_disj( 0_db );

   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "peano" + "succ"), 7_db ) );
   
   edit. apply_disj( 0_db );
   
   edit. apply_proof( term( prf_contr, 0_db, 7_db ) );
   edit. setfocus( 0 );
   edit. apply_proof( term( prf_contr, 0_db, 2_db ) );
   edit. setfocus( 0 );

   edit. apply_disj ( 2_db );

   edit. apply_proof( term( prf_contr, 0_db, 6_db) );
   edit. setfocus( 0 );

   edit. apply_abbreviate( term( prf_repl, 0_db, 4_db ));
   edit. apply_abbreviate( term( prf_repl, 2_db, 0_db ));
   edit. apply_abbreviate( term( prf_and2, 0_db ) );

   edit. apply_proof( term( prf_false, 0_db ) );
   edit. setfocus( 0 );

   edit. apply_disj( 0_db );

   edit. apply_exists( 0_db );
   
   edit. apply_abbreviate( term( prf_and2, 0_db ) );
   edit. apply_abbreviate( term( prf_and1, 0_db ) );
   edit. apply_abbreviate( term( prf_and2, 1_db ) );

   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "plus" + "succ"), 10_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, 10_db ) );
   edit. setfocus( 0 );
   edit. apply_abbreviate( term( prf_inst, 0_db, 6_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 7_db ) ) );
   edit. setfocus( 0 );

   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "plus" + "succ"), apply( "succ"_ident, 14_db ) ) );
   edit. apply_disj( 0_db );
   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "peano" + "succ" ), 16_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, 16_db ) );
   edit. setfocus( 0 );
   edit. apply_proof( term( prf_contr, 0_db, 2_db ) );
   edit. setfocus( 0 );
   edit. apply_abbreviate( term( prf_inst, 0_db, 10_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 11_db ) ) );
   edit. setfocus( 0 );
   
   edit. apply_disj( 9_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 12_db ) ) );
   edit. setfocus( 0 );

   edit. apply_abbreviate( term( prf_repl, term( prf_repl, 0_db, 5_db ), 1_db ) );
   edit. apply_abbreviate( term( prf_repl, 0_db, term( prf_and2, 10_db ) ) );
   edit. apply_proof( term( prf_false, 0_db ) );
   edit. setfocus( 0 );

   edit. apply_exists( term( prf_and2, 4_db ), "y" );
   edit. apply_abbreviate( term( prf_inst, 2_db, 1_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 2_db ) ) );
   edit. setfocus( 0 );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 3_db ) ) );
   edit. setfocus( 0 );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and2, 3_db ) ) );
   edit. setfocus( 0 );
   edit. show( std::cout, { } );
#endif

#if 1 // Start proof plus::com 
   
   bel. add( identifier( ) + "plus" + "com",
      belief(
         bel_thm,
         forall( { "x", type( sel_set ) },
                 implies( 
                    apply( "nat"_ident, 0_db),
                    forall( { "y", type( sel_set ) },
                             implies( apply( "nat"_ident, 0_db ),
                                      apply( "plus"_ident, 1_db, 0_db ) == apply( "plus"_ident, 0_db , 1_db ) 
                             )
                    )
                 )
         ), 
         term( sel_lambda, term( prf_unfinished ), {{ "goal", type( sel_belief ) }} )
      )
   );

   ind = bel. find( identifier( ) + "plus" + "com");
   if( ind >= bel. size( ))
   {
      std::cout << "did not find the theorem\n";
      return;
   }

   thm = bel. at( ind ). second. view_thm( ). form( );
   edit = logic::proofeditor( &bel, ind, !thm );

   edit. apply_exists( 0_db );
   edit. apply_abbreviate( term( prf_inst,
                                 term( sel_ident, identifier( ) + "peano" + "induction" ),
                                 term( sel_lambda,
                                       implies( apply( "nat"_ident, 0_db),
                                                apply( "plus"_ident, 2_db, 0_db ) == apply( "plus"_ident, 0_db, 2_db )),
                                       { { "z", type( sel_set ) } })) );

   // peano induction part 1
   edit. apply_disj( 0_db );
   
   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "plus" + "zero" ), 3_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 4_db ) ) );
   edit. setfocus( 0 );
   
   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "plus" + "zero" + "rev" ), 5_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 6_db) ) );
   edit. setfocus( 0 );

   edit. apply_abbreviate( term( prf_repl, 0_db, term( prf_repl, 2_db, term( prf_and2, 4_db ) ) ) );
   edit. apply_proof( term( prf_false, 0_db ) );
   edit. setfocus( 0 );

   // peano induction part 2

   edit. apply_disj( 0_db );
   edit. apply_exists( 0_db );

   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "plus" + "succ" ), 6_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 7_db ) ) );
   edit. setfocus( 0 );
   edit. apply_abbreviate( term( prf_inst, 0_db,  3_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 4_db ) ) );
   edit. setfocus( 0 );

   edit. apply_abbreviate( term( prf_inst, term( sel_ident, identifier( ) + "plus" + "succ" + "rev" ), 5_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 6_db ) ) );
   edit. setfocus( 0 );
   edit. apply_abbreviate( term( prf_inst, 0_db, 12_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 13_db ) ) );
   edit. setfocus( 0 );

   edit. apply_abbreviate( term( prf_and1, term( prf_and2, 8_db ) ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 10_db ) ) );
   edit. setfocus( 0 );

   edit. apply_abbreviate( term( prf_repl, 0_db, 6_db ) );
   edit. apply_abbreviate( term( prf_repl, 0_db, 3_db ) );
   edit. apply_abbreviate( term( prf_and2, term( prf_and2, term( prf_and2, 12_db ) ) ) );
   edit. apply_proof( term( prf_contr, 0_db, 1_db ) );
   edit. setfocus( 0 );

   // peano induction part 3

   edit. apply_exists( term( prf_and2, 3_db ), "y" );
   edit. apply_abbreviate( term( prf_and2, 0_db ) );

   edit. apply_abbreviate( term( prf_inst, 3_db, 2_db ) );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 3_db ) ) );
   edit. setfocus( 0 );
   edit. apply_disj( 0_db );
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 4_db ) ) );
   edit. setfocus( 0 );
   
   edit. apply_proof( term( prf_contr, 0_db, term( prf_and2, 4_db ) ) );
   edit. setfocus( 0 );
   edit. show( std::cout, { } );
#endif
#endif
#endif
}

void tests::prove_kuratowski( )
{
   using namespace logic;

#if 0
   beliefstate bel;
   add_kuratowski( bel );

   pretty::print( std::cout, bel );
   check_everything( std::cout, bel );

   size_t ind = bel. find( identifier( ) + "kuratowski" + "single" );
   if( ind >= bel. size( ))
   {
      std::cout << "did not find the theorem\n";
      return;
   }

   auto thm = bel. at( ind ). second. view_thm_file( ). form( );
   proofeditor edit( &bel, ind, !thm );

   edit. apply_exists( 0_db, "x" );
   edit. apply_exists( 0_db, "y" );

   edit. apply_disj( term( prf_inst, 
                       term( prf_ext1, term( prf_and1, 0_db )), 3_db ) ); 

   edit. apply_proof( term( prf_false, term( prf_and1, 0_db )));
   edit. setfocus(0);

   edit. apply_disj( 0_db );

   edit. apply_proof( term( prf_contr, term( prf_and2, 2_db ), 0_db ));

   edit. setfocus(0);

   edit. apply_proof( term( prf_false, 0_db ));
   edit. setfocus(0);

   edit. show( std::cout, { } );

   ///////////////////////////////////////////////

   std::cout << "-----------------------------\n";

   ind = bel. find( identifier( ) + "kuratowski" + "merge" );
   if( ind >= bel. size( ))
   {
      std::cout << "did not find the theorem\n";
      return;
   }

   thm = bel. at( ind ). second. view_thm_file( ). form( );
   edit = proofeditor( &bel, ind, !thm );

   edit. apply_exists( 0_db, "x" );
   edit. apply_exists( 0_db, "y" );
   edit. apply_exists( 0_db, "z" );

   
   edit. apply_abbreviate( term( prf_ext1, term( prf_and1, 0_db )), "forall" );

   edit. apply_disj( term( prf_and2, 1_db ));


   edit. apply_disj( term( prf_inst, 1_db, 5_db ) );
   edit. apply_proof( term( prf_false, term( prf_and1, 0_db )));
   edit. setfocus(0);

   edit. apply_disj( 0_db );

   edit. show( std::cout, {  } );
   
   edit. apply_proof( term( prf_false, term( prf_repl, 0_db, 2_db )));
   edit. setfocus(0);

   edit. apply_proof( term( prf_false, 0_db ));
   edit. setfocus(0);

   edit. apply_abbreviate( term( prf_inst, 1_db, 3_db ));

   edit. apply_disj( 0_db );

   edit. apply_proof( term( prf_false, term( prf_and1, term( prf_and2, 0_db ))) );

   edit. setfocus(0);

   edit. apply_disj( 0_db );

   edit. apply_proof( term( prf_false, term( prf_repl, 0_db, 3_db )) );

   edit. setfocus(0);

   edit. apply_proof( term( prf_false, 0_db ));

   edit. show( std::cout, {} );

   edit. setfocus(0);

   ///////////////////////////////////////////////

   std::cout << "-----------------------------\n";

   ind = bel. find( identifier( ) + "kuratowski" + "insert" );
   if( ind >= bel. size( ))
   {
      std::cout << "did not find the theorem\n";
      return;
   }

   thm = bel. at( ind ). second. view_thm_file( ). form( );
   edit = proofeditor( &bel, ind, !thm );

   edit. apply_exists( 0_db, "x" );
   edit. apply_exists( 0_db, "y" );
   edit. apply_exists( 0_db, "y" );

   edit. show( std::cout, {} );
#endif 
}

void tests::prove_von_neumann( )
{
   using namespace logic;

#if 0
   beliefstate bel;
   add_von_neumann( bel );

   pretty::print( std::cout, bel );
   check_everything( std::cout, bel );

   size_t ind = bel. find( identifier( ) + "von" + "neumann" + "subset" );
   if( ind >= bel. size( ))
   {
      std::cout << "did not find the theorem\n";
      return;
   }

   auto thm = bel. at( ind ). second. view_thm_file( ). form( );
   proofeditor edit( &bel, ind, !thm );

   edit. apply_exists( 0_db );

   edit. apply_proof( term( prf_contr,
      term( prf_and1, 
         term( prf_exp, term( prf_and1, 0_db ), identifier( ) + "von" + "neumann" + "omega1",
               position( ) )),
      term( prf_and2, 0_db )));

   edit. show( std::cout, { } );
#endif
   //////////////////////////////////////////////////////////////

#if 0
   ind = bel. find( identifier( ) + "von" + "neumann" + "smallest" );
   if( ind >= bel. size( ))
   {
      std::cout << "did not find the theorem\n";
      return;
   }

   thm = bel. at( ind ). second. view_thm_file( ). form( );
   edit = proofeditor( &bel, ind, !thm );

   edit. apply_exists( 0_db );

   edit. apply_abbreviate( term( prf_exp, term( prf_and1, 0_db ),
                                 identifier( ) + "von"+"neumann"+"clos1",
                                 position( ) ));

   edit. apply_abbreviate( term( prf_exp, term( prf_and2, 1_db ),
                                 identifier( ) + "von"+"neumann"+"omega1",
                                 position( ) )); 

   edit. apply_exists( 0_db );

   edit. apply_abbreviate( term( prf_exp,
                              term( prf_exp, term( prf_and1, 0_db ),
                                    identifier( ) + "von" + "neumann" + "clos1",
                                    position( ) ),
                              identifier( ) + "von"+"neumann"+"intersect",
                              position( )) );

   edit. apply_abbreviate( term( prf_inst, term( prf_and2, 0_db ), 6_db ));

   edit. apply_disj( 0_db );

   edit. apply_disj( 0_db );

   // edit. apply_proof( term( prf_contr, 0_db, term( prf_and1, 7_db )));

   edit. setfocus(0);

   edit. apply_exists( 0_db );

   edit. apply_disj( term( prf_inst, term( prf_and2, 9_db ), 1_db ));
 
   // edit. apply_proof( term( prf_contr, term( prf_and1, 1_db ), 0_db ));

   edit. setfocus(0);

   // edit. apply_proof( term( prf_contr, term( prf_and2, 1_db ), 0_db ));

   edit. setfocus(0);

   // edit. apply_proof( term( prf_contr, term( prf_and2, 3_db ), 0_db ));
   edit. show( std::cout, {} );

   edit. setfocus(0);

   edit. show( std::cout, {} );

#endif
   // Current Focus
}

#endif

void tests::truthtables( )
{
   using namespace logic;

   auto O = type( type_obj );
   auto T = type( type_form );

   auto O2T = type( type_func, T, { O } );
   auto O2O = type( type_func, O, { O } );

   auto OO2T = type( type_func, T, { O, O } );
   auto OOO2T = type( type_func, T, { O, O, O } );
   auto tp = type( type_func, T, {O} );
   term from = exists( {{ "x", logic::type_obj }}, apply( "P"_unchecked, { 0_db } ) && apply( "Q"_unchecked, { 0_db } ));
   auto b = term( op_kleene_and, { apply( "P"_unchecked, { 0_db } ), apply( "Q"_unchecked, { 0_db } ) } );
   term into = term( op_kleene_exists, b, { { "x", logic::type_obj }} );

   logic::context ctxt;
   logic::beliefstate blfs;

   // std::cout << from << "\n";
   pretty::print( std::cout, blfs, ctxt, from );
   // std::cout << into << "\n";
   pretty::print( std::cout, blfs, ctxt, into );
   std::cout << "\n\n";
   semantics::check_preceq( { { identifier( ) + "P", O2T }, { identifier( ) + "Q", O2T }}, from, into );
}

#if 0
#if 0

void tests::parser( ) {
   logic::beliefstate blfs;
   logic::proofeditor editor( &blfs,  blfs. size( ), logic::term( logic::sel_false ) );
   parsing::tokenizer token;
   parsing::parser prs( token, blfs, editor );
   prs. debug = 0;
   prs. checkattrtypes = 0;
   prs. checkmovable = 0;

   while( true )
   {
      std::cout << editor. focus << "\n";
      std::cout << ">>> ";
      prs. ensurelookahead( );

      if( prs. getlookahead( ). type == parsing::sym_EOF )
      {
         std::cerr << "   end of file is reached.\n";
         break;
      }

      //std::cout << "\n~~~" << parsing::sym_start << "~~~\n";

      const auto res = prs. parse( parsing::sym_start );
      //std::cout << "\n";

      //std::cout << "   parsing res: " << res << "\n";
      prs. ensurelookahead( );
      //std::cout << "   lookahead: " << prs. getlookahead( ) << "\n";

      if( res. type == parsing::sym_command &&
          prs. getlookahead( ). type == parsing::sym_SEMICOLON )
      {
         //std::cout << "\nstatement parsed successfully.";
         std::cout << "\n----------------------------------\n";
         editor. show( std::cout );
         pretty::print( std::cout, blfs );
         editor. check.localbeliefs;
         std::cout << "Local Belief: \n";
         
         logic::context ctxt;
         editor. check. extendcontext( ctxt, editor. focus );
         auto names = pretty::getnames( ctxt );
         const size_t ctxt_size = ctxt. size( );

         std::cout << "Proof term:\n";
         pretty::print(std::cout, names, editor. check. topterm ); std::cout << "\n";
         for( auto e: editor.check. localbeliefs)
         {
            std::cout << "\t" << e. first << " -> "; pretty::print( std::cout, names, e. second. at( 0 ) );
            std::cout << "\n";
         }

         std::cout << "\n----------------------------------\n\n";
      }
      else
      {
         std::cout << "   error:\n"; 
         while( prs. getlookahead( ). type != parsing::sym_SEMICOLON &&
                pr.s getlookahead( ). type != parsing::sym_EOF )
         {
            std::cout << "'"<< prs. getlookahead( ) <<"'\n";
            prs. resetlookahead( );
            prs. ensurelookahead( );
         }
      }
      
      if( prs. getlookahead( ). type == parsing::sym_SEMICOLON )
         prs. resetlookahead( );

      prs. reset( );
   }
}
#endif

#endif
