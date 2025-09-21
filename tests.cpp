
#include "tests.h"
#include "errorstack.h"

#include "logic/replacements.h" 
#include "logic/pretty.h"
#include "logic/cmp.h"
#include "logic/termoperators.h"

#include "calc/proofterm.h"
#include "calc/proofchecking.h"
#include "calc/kleening.h"
#include "calc/alternating.h"
#include "calc/removelets.h"
#include "calc/expander.h"
#include "calc/projection.h"
#include "calc/proofoperators.h"
#include "calc/clauseset.h"

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


void tests::clausify( logic::beliefstate& blfs, errorstack& err )
{
   std::cout << "testing clausify\n";

   using namespace logic;
   type O = type( logic::type_obj );
   type T = type( logic::type_form );
   type O2T = type( type_func, T, { O } );
   type O2O = type( type_func, O, { O } );

   type Seq = type( type_unchecked, identifier( ) + "Seq" );
   type X = type( type_unchecked, identifier( ) + "X" );

   if constexpr( false )
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

      form = 5_db; 
      // form = prop( !form );
      std::cout << "the formula is " << form << "\n";

      form = calc::alternating( form, logic::op_kleene_or, 2 );

      {
         context ctxt; 
         std::cout << "result = ";
         std::cout << form << "\n";

         // pretty::print( std::cout, blfs, ctxt, form );
      }
   }

   if constexpr( false ) 
   {
      std::cout << "\n\n";
      std::cout << "testing removelets\n";
      auto f = ( 0_db == 2_db );
      f = apply( "ppp"_unchecked, { 0_db, 1_db, 2_db } );
      f = term( op_let, { "zz", O }, apply( "gg"_unchecked, { 0_db } ), f );
      f = !f;
      f = term( op_let, { "yy", T }, apply( "ff"_unchecked, { 1_db } ), f );
      f = term( op_forall, f, {{ "x", T }, { "y", O2O }} ); 
      f = term( op_exists, f, {{ "a", O }, { "b", T }} );
      f = term( op_lambda, f, {{ "hallo", O2T }} );
      {
         context ctxt;
         pretty::print( std::cout, blfs, ctxt, f );
      }

      calc::sequent seq( blfs ); 
      logic::context ctxt;
      f = removelets( seq, ctxt, std::move(f) ); 
      {
         context ctxt; 
         pretty::print( std::cout, blfs, ctxt, f );
      }
      return; 
   }

   if constexpr( true )
   {
      std::cout << "\n\n";
      std::cout << "Testing Expand\n";
      auto f = ( 0_db == 2_db );
      f = apply( "ppp"_unchecked, { "serial"_unchecked, term( op_exact, exact(38)), 
                                          term( op_exact, exact(42)) } );
      f = term( op_let, { "zz", O }, apply( "gg"_unchecked, { 0_db } ), f );
      f = !f;
      f = term( op_let, { "yy", T }, apply( "ff"_unchecked, { 1_db } ), f );
      f = term( op_forall, f, {{ "x", T }, { "y", O2O }} );
      f = term( op_exists, f, {{ "a", O }, { "b", T }} );
      f = term( op_lambda, f, {{ "hallo", O2T }} );
      {
         context ctxt;
         pretty::print( std::cout, blfs, ctxt, f );
         std::cout << "\n";
      }
      auto exp = calc::expander( identifier( ) + "serial", 2, blfs, err );
      std::cout << exp << "\n";
      f = outermost( exp, f, 0 );
      {
         context ctxt;
         pretty::print( std::cout, blfs, ctxt, f );
      }
      std::cout << exp << "\n";
      return;
   }
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

}


void tests::simplify( )
{
   std::cout << "testing simplify\n";

   using namespace logic;

   type O = type( logic::type_obj );
   type T = type( logic::type_form );
   type O2T = type( type_func, T, { O } );
   type O2O = type( type_func, O, { O } );
   type OT2O = type( type_func, O, { O, T } );

   auto cl1 = term( logic::op_kleene_or,
      { "A"_unchecked, "B"_unchecked, "C"_unchecked } );
   auto cl2 = term( logic::op_kleene_or,
      { ! "A"_unchecked , "B"_unchecked, "C"_unchecked } );
   auto cl3 = term( logic::op_kleene_or,
      { "b1"_unchecked == "b2"_unchecked, "S"_unchecked } );
   auto cl4 = term( logic::op_kleene_or, 
      { "b2"_unchecked == "b3"_unchecked, "S"_unchecked } );
   auto cl5 = term( logic::op_kleene_or,
      { ! "R"_unchecked } );
   auto cl6 = term( logic::op_kleene_or,
      { ! prop( "C"_unchecked ), "B"_unchecked } );

   auto conj = term( logic::op_kleene_and, { cl1, cl5, cl2, cl6, cl3, cl4 } );
   std::cout << conj << "\n";

   calc::clauseset cls;
   bool b = cls. insert( conj );
   std::cout << b << "\n\n";
   std::cout << cls << "\n";
   cls. fully_simplify( );
   std::cout << cls << "\n";
   std::cout << cls. conjunction( ) << "\n";

}


void tests::cmp( )
{
   std::cout << "testing compare\n";

   using namespace logic;

   std::cout << ( ( 1_db == 3_db ) <=> ( 1_db == 3_db ) ) << "\n";

   type O = type( logic::type_obj );
   type T = type( logic::type_form );
   type O2T = type( type_func, T, { O } );
   type O2O = type( type_func, O, { O } );
   type OT2O = type( type_func, O, { O, T } );

   type Seq = type( type_unchecked, identifier( ) + "Seq" );
   type X = type( type_unchecked, identifier( ) + "X" );

   auto tm1 = "aba"_unchecked || 3_db;
   tm1 = term( op_lambda, tm1, { { "x", T }, { "y", Seq }, { "z", O }} );

   auto tm2 = "aba"_unchecked || 3_db;
   tm2 = term( op_lambda, tm2, { { "x", T }, { "y", Seq }, { "t", O }} );
 
   tm1 = apply( tm2, { 2_db, "bba"_unchecked, 1_db } );
   tm2 = apply( tm1, { 2_db, "bba"_unchecked, term( op_exact, exact(12)) } );
   std::cout << ( tm1 <=> tm2 ) << "\n";
   std::cout << "weights\n";
   std::cout << weight(tm1) << "\n" << weight( tm2 ) << "\n";
  
   // bool b = equal( tm1, tm2 );
   // std::cout << "result = " << b << "\n"; 

   tm1 = lift( tm1, 1 );
   tm2 = lift( tm2, 4 );
   // b = equal( tm1, 6, tm2, 3, 0 );
   // std::cout << "lifted result = " << b << "\n";
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


void tests::betareduction( logic::beliefstate& blfs, errorstack& err ) 
{
   using namespace logic;

   type O = type( type_obj );
   type T = type( type_form );

   type O2O = type( type_func, O, { O } );
   type O2T = type( type_func, T, { O } );
   
   logic::betareduction beta;
   std::cout << beta << "\n";

   term body = term( op_apply, "func"_unchecked, { 0_db, 1_db, 2_db, 3_db } );
   body = term( op_forall, body, {{ "haha", T }} ); 
   term lambda = term( op_lambda, body, { { "x", O }, { "y", O } } );

   auto first = term( op_apply, "first"_unchecked, { 1_db } ); 
   auto second = term( op_apply, "second"_unchecked, { 2_db } );
   auto third =  term( op_apply, "third"_unchecked, { 3_db } );

   term appl = term( op_apply, lambda, { first, second, third } );

   std::cout << "appl = " << appl << "\n";

   bool change = false;

   auto res = beta( appl, 0, change );
   std::cout << "res = " << res << "\n";
   std::cout << "change = " << change << "\n";
   std::cout << beta << "\n";

}

void tests::smallproofs( logic::beliefstate& blfs, errorstack& err )
{
   auto O = logic::type( logic::type_obj );
   auto T = logic::type( logic::type_form );
   auto Nat = logic::type( logic::type_unchecked, identifier( ) + "Nat" );

   using namespace calc;

   // This is the first proof that passed!

   auto id = identifier( ) + "resolve";

   const auto& f = blfs. getformulas( id );
   std::cout << f. size( ) << "\n";
   if( f. size( ) != 1 )
      throw std::runtime_error( "cannot continue" );

   auto seq = sequent( blfs );
   seq. assume( "initial", ! blfs. at( f. front( )). view_thm( ). frm( ));
   std::cout << seq << "\n";

   auto orelim2 = proofterm( prf_orelim,
                     proofterm( prf_forallelim,
                        proofterm( prf_ident, identifier( ) + "hyp0001" ), 1,
                        { "z0001"_unchecked } ), 0,
                  { { "ccc", proofterm( prf_conflict,
                       proofterm( prf_andintro, 
                       { proofterm( prf_ident, identifier( ) + "aaa0001" ),
                         proofterm( prf_ident, identifier( ) + "ccc0001" ) } )) },
                    { "ddd", proofterm( prf_conflict,
                       proofterm( prf_andintro, 
                       { proofterm( prf_ident, identifier( ) + "neg0001" ),
                         proofterm( prf_ident, identifier( ) + "ddd0001" ) } )) }} );

   auto orelim = proofterm( prf_orelim,
                    proofterm( prf_forallelim,
                       proofterm( prf_ident, identifier( ) + "hyp0001" ), 0,
                       { "z0001"_unchecked } ), 0,
                 { { "aaa", orelim2 },
                   { "bbb",
                      proofterm( prf_conflict,
                         proofterm( prf_andintro,
                            { proofterm( prf_ident, identifier( ) + "neg0001" ),
                              proofterm( prf_ident, identifier( ) + "bbb0001" ) } ))
                        }} );

   auto ref =
      proofterm( prf_existselim, 
         proofterm( prf_clausify,
            proofterm( prf_ident, identifier( ) + "initial0001" )), 0, 
         "hyp", proofterm( prf_existselim, 
                   proofterm( prf_ident, identifier( ) + "hyp0001" ), 2,
           "neg", orelim  ));

   ref. print( indentation(0), std::cout );

   auto ff = deduce( ref, seq, err );
   if( ff. has_value( ))
      std::cout << "proved this formula: " << ff. value( ) << "\n";

   auto mag1 = proofterm( prf_fake, "hans"_unchecked );
   auto mag2 = proofterm( prf_fake, "de"_unchecked ); 
   auto mag3 = proofterm( prf_fake, "nivelle"_unchecked );
   auto mag4 = proofterm( prf_fake, "hans"_unchecked == "jean"_unchecked );

   ref = proofterm( prf_andintro, { mag1, mag2, mag3, mag4 } );

   ref = proofterm( prf_cut, ref, "asm", 
            proofterm( prf_select, proofterm( prf_ident, identifier( ) + "asm" ), {1} ));

   ref. print( indentation(0), std::cout );
   
   ff = deduce( ref, seq, err );
   if( ff. has_value( ))
      std::cout << "proved this formula: " << ff. value( ) << "\n";

}


void tests::bigproof( logic::beliefstate& blfs, errorstack& err )
{
   auto O = logic::type( logic::type_obj );
   auto T = logic::type( logic::type_form );
   auto Nat = logic::type( logic::type_unchecked, identifier( ) + "Nat" );

   using namespace calc;

   auto id = identifier( ) + "just";
   const auto& f = blfs. getformulas( id );
   std::cout << f. size( ) << "\n";
   if( f. size( ) != 1 )
      throw std::runtime_error( "cannot continue" );

   auto seq = sequent( blfs );
   std::cout << "start of a big proof --------------------------\n";

   seq. assume( "initial", ! blfs. at( f. front( )). view_thm( ). frm( ));
   std::cout << seq << "\n";

   logic::term indhyp = logic::term( logic::op_false );  // Q in the paper. 
   {
      using namespace logic;
      auto disj1 = 
         1_db == apply( "0"_unchecked, { 3_db } ) &&
         0_db == apply( "0"_unchecked, { 2_db } );

      // Left and right of the lazy-and inside the exists:

      auto la1 =
         apply( "gen"_unchecked, { 5_db, 1_db } ) && 
         apply( "gen"_unchecked, { 4_db, 0_db } );

      auto la2 = 
         apply( "minhomrel"_unchecked, { 5_db, 4_db, 1_db, 0_db } ) &&
         3_db == apply( "succ"_unchecked, { 5_db, 1_db } ) &&
         2_db == apply( "succ"_unchecked, { 4_db, 0_db } );

      auto disj2 = exists( { { "y1", O }, { "y2", O }}, lazy_and( la1, la2 ));

      indhyp = disj1 || disj2; 
      indhyp = lambda( {{ "x1", O }, { "x2", O }}, indhyp );
      indhyp = lambda( {{ "n1", Nat }, { "n2", Nat }}, indhyp );
   }

   auto magcontr = proofterm( prf_fake, logic::op_false );
   auto exists = clausify( "initial0001"_assumption ); 

   auto prf3 = proofterm( prf_ident, identifier( ) + "forall0001" );
   auto inst = apply( "Q0001"_unchecked, { "s0001"_unchecked, "s0002"_unchecked } );

   auto base = "base0001"_assumption;
   base = expand( "Q0001", 0, base );
   base = clausify( base );
   base = conflict( base );
   base = show( "base case", base );

   auto step = magcontr;
   step = show( "step case", step );
   step = existselim( "step0001"_assumption, 0, "exists", step );


   auto goal2 = "alt0002"_assumption;
   // goal2 = proofterm( prf_expand, identifier( ) + "Q0001", 0, goal2 );
   goal2 = expand( "homrel", 0, goal2 );
   goal2 = clausify( goal2 );
   goal2 = proofterm( prf_orelim, goal2, 0,
      { { "base", base }, { "step", step }} );

   goal2 = proofterm( prf_show, "the main part", goal2 );
 
   auto goal3 = expand( "Q0001", 0, "alt0003"_assumption );
   goal3 = show( "(the final goal, very easy I think)", goal3 );

   prf3 = proofterm( prf_forallelim, prf3, 0, { inst } );
   prf3 = proofterm( prf_orelim, prf3, 0, 
      { { "alt1", magcontr }, { "alt2", goal2 }, { "alt3", goal3 }} );

   prf3 = proofterm( prf_define, "Q", indhyp, prf3 );

   auto disj = proofterm( prf_ident, identifier( ) + "main0001" );
   disj = expand( "minhomrel", 0, disj );
   disj = expand( "inductive", 0, disj );
   disj = proofterm( prf_show, "expanded disj", disj );

   auto prf2 = proofterm( prf_orelim, disj, 2, {{ "forall", prf3 }} );
 
   auto res = 
      deduce( proofterm( prf_existselim, exists, 0, "main", prf2 ), seq, err );

   if( res. has_value( ))
      std::cout << "evaluation of main proof returned: " << res. value( ) << "\n";
   else
      std::cout << "(evaluation of main proof failed)\n";
}


#if 0

void tests::unification( const logic::beliefstate& blfs, errorstack& err ) 
{
   using namespace logic;

   term t1 = apply( term( op_exact, exact(11)), { 5_db, 5_db } );
   term t2 = apply( term( op_exact, exact(11)), { 4_db, "aa"_unchecked } );

   calc::unifsubst subst;

   calc::forallstarts univ = { { 0, 2 }, { 1, 1 }};
   auto b = calc::unify( subst, univ, 
                         calc::termorig( t1, 0 ), 3, 
                         calc::termorig( t2, 1 ), 2 );

   if(b) 
   {
      std::cout << "succeeded with\n";
      std::cout << subst << "\n";
   }
   else
      std::cout << "failed\n";
}
#endif

#if 0
void tests::prove_pluscom( )
{
   using namespace logic;
#if 0
   // Pluscom: 

   return;

   edit. apply_proof( term( prf_axiom, { 0_db, 1_db, 2_db } ));
   // Unfinished Point 

   edit. setfocus(2);

   std::cout << edit. check. nr_unfinished( ) << "\n";

   edit. show( std::cout, { } );
#if 0
#if 1  // Start proof plus::succ:rev
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
#endif
#endif
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

