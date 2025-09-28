
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
   cls. insert( conj );
   std::cout << cls << "\n";
   cls. fully_simplify( );
   std::cout << cls << "\n";
   std::cout << cls. getformula( ) << "\n";

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

   if constexpr( false ) 
   {
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
                     { { "ccc", proofterm( prf_simplify,
                          proofterm( prf_andintro, 
                          { proofterm( prf_ident, identifier( ) + "aaa0001" ),
                            proofterm( prf_ident, identifier( ) + "ccc0001" ) } )) },
                       { "ddd", proofterm( prf_simplify,
                          proofterm( prf_andintro, 
                          { proofterm( prf_ident, identifier( ) + "neg0001" ),
                            proofterm( prf_ident, identifier( ) + "ddd0001" ) } )) }} );

      auto orelim = proofterm( prf_orelim,
                       proofterm( prf_forallelim,
                          proofterm( prf_ident, identifier( ) + "hyp0001" ), 0,
                          { "z0001"_unchecked } ), 0,
                    { { "aaa", orelim2 },
                      { "bbb",
                         proofterm( prf_simplify,
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
         std::cout << "proved this formula: " << ff. value( ) << "\n\n";

      auto fake1 = proofterm( prf_fake, "hans"_unchecked );
      auto fake2 = proofterm( prf_fake, "de"_unchecked ); 
      auto fake3 = proofterm( prf_fake, "nivelle"_unchecked );
      auto fake4 = proofterm( prf_fake, "hans"_unchecked == "jean"_unchecked );

      ref = andintro( { fake1, fake2, fake3, fake4 } );

      ref = proofterm( prf_cut, ref, "asm", 
               proofterm( prf_select, proofterm( prf_ident, identifier( ) + "asm" ), {1} ));

      ref. print( indentation(0), std::cout );
   
      ff = deduce( ref, seq, err );
      if( ff. has_value( ))
         std::cout << "proved this formula: " << ff. value( ) << "\n\n";
   }


   {
      // second (or first) complete proof:

      auto id = identifier( ) + "minhomrel_succ";

      const auto& f = blfs. getformulas( id );
      std::cout << f. size( ) << "\n";
      if( f. size( ) != 1 )
         throw std::runtime_error( "cannot continue minhomrel_succ" );
     
      auto seq = sequent( blfs ); 
      seq. assume( "goal", ! blfs. at( f. front( )). view_thm( ). frm( ));
      std::cout << seq << "\n";

      auto ref = clausify( "goal0001"_assumption ); 

      auto sub2 = "skolem0001"_assumption;
      sub2 = select( {2}, sub2 );
      sub2 = expand( "minhomrel", 0, sub2 ); 
      sub2 = expand( "minimal", 0, sub2 );
      sub2 = clausify( sub2 );
      sub2 = proofterm( prf_forallelim, sub2, 0, { "R0001"_unchecked } );
 
      auto sub = "skolem0001"_assumption;
      sub = select( {3}, sub );
      sub = expand( "minhomrel", 0, sub );
      sub = expand( "minimal", 0, sub );
      sub = clausify( sub );

      auto homrel = "skolem0002"_assumption;
      homrel = select( {1}, homrel );
      homrel = expand( "homrel", 0, homrel );
      homrel = clausify( homrel );
      homrel = select( {1}, homrel );
      homrel = proofterm( prf_forallelim, homrel, 0, { "x0001"_unchecked, "x0002"_unchecked } );

      sub2 = andintro( { sub2, homrel, "skolem0002"_assumption, "skolem0001"_assumption } );
      sub2 = simplify( sub2 );
      sub2 = show( "FINAL SIMPLIFICATION", sub2 ); 

      sub = proofterm( prf_existselim, sub, 0, "skolem", sub2 );
      ref = proofterm( prf_existselim, ref, 0, "skolem", sub );

      ref. print( indentation(0), std::cout );

      auto ff = deduce( ref, seq, err );
      if( ff. has_value( ))
         std::cout << "proved this formula: " << ff. value( ) << "\n\n";
      else
         std::cout << "(proved nothing)\n\n";
   }
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

   auto fakecontr = proofterm( prf_fake, logic::op_false );
   auto exists = clausify( "initial0001"_assumption ); 

   auto prf3 = proofterm( prf_ident, identifier( ) + "forall0001" );
   auto inst = apply( "Q0001"_unchecked, { "s0001"_unchecked, "s0002"_unchecked } );

   auto base = "base0001"_assumption;
   base = expand( "Q0001", 0, base );
   base = clausify( base );
   base = simplify( base );
   base = show( "base case", base );

   auto step = select( { 3 }, "exists0001"_assumption ); 
   step = expand( "Q0001", 0, step );
   step = clausify( step );
   step = proofterm( prf_forallelim, step, 1, { "x0003"_unchecked, "x0004"_unchecked } );
   step = simplify( step );

   auto inst1 = proofterm( prf_forallelim, clausify( "gen_succ"_assumption ), 0, 
                           { "s0001"_unchecked, "y0001"_unchecked } );
   auto inst2 = proofterm( prf_forallelim, clausify( "gen_succ"_assumption ), 0,
                           { "s0002"_unchecked, "y0002"_unchecked } );
   auto inst3 = clausify( "minhomrel_succ"_assumption );
   inst3 = proofterm( prf_forallelim, inst3, 0, { "s0001"_unchecked, "s0002"_unchecked, 
                                                  "y0001"_unchecked, "y0002"_unchecked } );

   auto left1 = "exists0001"_assumption;
   left1 = select( {3}, left1 );
   left1 = expand( "Q0001", 0, left1 );
   left1 = clausify( left1 );
   left1 = proofterm( prf_forallelim, left1, 1, { "x0003"_unchecked, "x0004"_unchecked } );
   auto thm = proofterm( prf_forallelim, clausify( "minhomrel_zero"_assumption ), 0, { "s0001"_unchecked, "s0002"_unchecked } );

   left1 = andintro( { left1, thm, "exists0001"_assumption, "base0002"_assumption } );
   left1 = simplify( left1 );
   left1 = show( "little step to the left", left1 );

   step = orelim( clausify( expand( "Q0001", 0, "exists0001"_assumption )), 2, 
                  "base", left1,
                  "step", existselim( "step0002"_assumption, 0, "aaaa", show( "the little step to right", 
                simplify( andintro( { step, "aaaa0001"_assumption, inst1, inst2, inst3 } )) )));
   // I believe the proof is on the right track. We also need for minhomrel. 

   step = existselim( "step0001"_assumption, 0, "exists", step );

   auto goal2 = "alt0002"_assumption;
   // goal2 = proofterm( prf_expand, identifier( ) + "Q0001", 0, goal2 );
   goal2 = expand( "homrel", 0, goal2 );
   goal2 = clausify( goal2 );
   goal2 = orelim( goal2, 0, "base", base, "step", step );

   auto goal3 = expand( "Q0001", 0, "alt0003"_assumption );
   goal3 = show( "(the final goal, contradicts main0001 I think)", goal3 );

   prf3 = proofterm( prf_forallelim, prf3, 0, { inst } );
   prf3 = proofterm( prf_orelim, prf3, 0, 
      { { "alt1", show( "looks like a type condition", fakecontr ) }, { "alt2", goal2 }, { "alt3", goal3 }} );

   prf3 = proofterm( prf_define, "Q", indhyp, prf3 );

   auto disj = proofterm( prf_ident, identifier( ) + "main0001" );
   disj = expand( "minhomrel", 0, disj );
   disj = expand( "minimal", 0, disj );
   disj = proofterm( prf_show, "expanded disj", disj );

   auto prf2 = proofterm( prf_orelim, disj, 2, {{ "forall", prf3 }} );

   prf2. print( indentation( ), std::cout ); 
 
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

