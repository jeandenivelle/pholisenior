
#include "tests.h"

#include "errorstack.h"

#include "logic/termoperators.h"
#include "logic/kbo.h"
#include "logic/structural.h"

#include "reso/transformations.h"

#include "logic/replacements.h" 

#if 0
// #include "logic/normalization.h"
#endif

void tests::add_strict_prod( logic::beliefstate& bel )
{
   using namespace logic;
     
   auto O = type( type_obj );
   auto T = type( type_truthval );

   auto O2T = type( type_func, T, { O } );  
   auto OO2T = type( type_func, T, { O, O } );
   auto OOO2T = type( type_func, T, { O, O, O } );

   // strict1 :

   {
      auto s1 = lambda( { { "P", O2T } }, 
      forall( {{ "x1", O }}, prop( apply( 1_db, { 0_db } )) ));

      auto tp = type( type_func, T, { O2T } );

      bel. append( belief( bel_def, identifier( ) + "strict", s1, tp ));
   }

   // strict2 :

   {
      auto s2 = lambda( { { "P", OO2T } }, 
         forall( {{ "x1", O }, { "x2", O }}, 
         prop( apply( 2_db, { 1_db, 0_db } )) ));

      auto tp = type( type_func, T, { OO2T } );

      bel. append( belief( bel_def, identifier( ) + "strict", s2, tp ));
   }
 
   // strict3 :

   {
      auto s3 = lambda( {{ "P", OOO2T }},
         forall( {{ "x1", O }, { "x2", O }, { "x3", O }}, 
         prop( apply( 3_db, { 2_db, 1_db, 0_db } )) ));

      auto tp = type( type_func, T, { OOO2T } );

      bel. append( belief( bel_def, identifier( ) + "strict", s3, tp ));
   }

   // stricton1 :

   {
     auto s1 = implies(
        apply( 2_db, { 0_db } ),
        prop( apply( 1_db, { 0_db } )));

      s1 = forall( {{ "x1", O }}, s1 );
      s1 = lambda( {{ "P", O2T }, { "Q", O2T }}, s1 );

      auto tp = type( type_func, T, { O2T, O2T } );

      bel. append( belief( bel_def, identifier( ) + "stricton", s1, tp ));
   }

   // stricton2 : 

   {
      auto s2 = implies( 
        apply( 3_db, { 1_db, 0_db } ),
        prop( apply( 2_db, { 1_db, 0_db } )));

      s2 = forall( {{ "x1", O }, { "x2", O }}, s2 );
      s2 = lambda( { { "P", OO2T }, { "Q", OO2T } }, s2 );

      auto tp = type( type_func, T, { OO2T, OO2T } );

      bel. append( belief( bel_def, identifier( ) + "stricton", s2, tp ));
   }

   // stricton3 :

   {
      auto s3 = implies(
        apply( 4_db, { 2_db, 1_db, 0_db } ),
        prop( apply( 3_db, { 2_db, 1_db, 0_db } )));

      s3 = forall( {{ "x1", O }, { "x2", O }, { "x3", O }}, s3 );
      s3 = lambda( { { "P", OOO2T }, { "Q", OOO2T } }, s3 );

      auto tp = type( type_func, T, { OOO2T, OOO2T } );

      bel. append( belief( bel_def, identifier( ) + "stricton", s3, tp ));
   }

   // prod2 :

   {
      auto prod2 = apply( 3_db, { 1_db } ) && apply( 2_db, { 0_db } );
      prod2 = lambda( {{ "x1", O }, { "x2", O }}, prod2 );
      prod2 = lambda( {{ "P1", O2T }, { "P2", O2T }}, prod2 );

      auto tp = type( type_func, type( type_func, T, { O, O } ), { O2T, O2T } );

      bel. append( belief( bel_def, identifier( ) + "prod", prod2, tp ));
   }

   // prod3 :

   {
      auto prod3 = apply( 5_db, { 2_db } ) && apply( 4_db, { 1_db } ) && 
                   apply( 3_db, { 0_db } );
      prod3 = lambda( {{ "x1", O }, { "x2", O }, { "x3", O }}, prod3 );
      prod3 = lambda( {{ "P1", O2T }, { "P2", O2T }, { "P3", O2T }}, prod3 ); 

      auto tp = type( type_func, type( type_func, T, { O, O, O } ), { O2T, O2T, O2T } );
    
      bel. append( belief( bel_def, identifier( ) + "prod", prod3, tp ));
   }

}


void tests::add_function( logic::beliefstate& bel )
{
#if 0
   using namespace logic;

   auto O = type( type_obj );
   auto T = type( type_truthval );

   auto O2T = type( type_func, T, { O } );
   auto OO2T = type( type_func, T, { O, O } );
   auto OOO2T = type( type_func, T, { O, O, O } );

   auto O2O = type( type_func, O, { O } );
   auto OO2O = type( type_func, O, { O, O } );
   auto OOO2O = type( type_func, O, { O, O, O } );

   // function1 :

   {
      auto bod = forall( { "x_1", O }, 
         implies( apply( 3_db, { 0_db } ), 
                  apply( 2_db, { apply( 1_db, { 0_db } ) } )));

      bod = lambda( { { "P", O2T }, { "Q", O2T }, { "f", O2O } }, bod );

      bel. add( identifier( ) + "function", belief( bel_def, bod, 
          type( type_func, T, { O2T, O2T, O2O } )) );
   }

   // function2:

   {
      auto bod = forall( { "x_1", O }, forall( { "x_2", O }, 
         implies( apply( 4_db, { 1_db, 0_db } ),
                  apply( 3_db, { apply( 2_db, { 1_db, 0_db } ) } ))));

      bod = lambda( { { "P", OO2T }, { "Q", O2T }, { "f", OO2O } }, bod );

      bel. add( identifier( ) + "function", belief( bel_def, bod,
          type( type_func, T, { OO2T, O2T, OO2O } )) );
   }

   // function3:

   {
      auto bod = forall( { "x_1", O }, forall( { "x_2", O }, forall( { "x_3", O }, 
         implies( apply( 5_db, { 2_db, 1_db, 0_db } ),
                  apply( 4_db, { apply( 3_db, { 2_db, 1_db, 0_db } ) } )))));

      bod = lambda( { { "P", OOO2T }, { "Q", O2T }, { "f", OOO2O } }, bod );

      bel. add( identifier( ) + "function", belief( bel_def, bod,
          type( type_func, T, { OOO2T, O2T, OOO2O } )) );
   }
#endif
}


void tests::add_unique( logic::beliefstate& blfs )
{
#if 0
   using namespace logic;

   auto O = type( type_obj );
   auto T = type( type_truthval );
   auto O2T = type( type_func, T, { O } );

   {
      auto atleast = forall( { "y", O }, apply( 1_db, { 0_db } ));
      atleast = lambda( { { "P", O2T } }, atleast );

      blfs. add( identifier( ) + "atleastone", belief( bel_def, atleast,  
         type( type_func, T, { O2T } ) ));
   }

   {
      auto atmost = forall( { "x1", O }, forall( { "x2", O },
         implies( apply( 2_db, { 1_db } ) && apply( 2_db, { 0_db } ),
                  1_db == 0_db )));
      atmost = lambda( { { "P", O2T } }, atmost );

      blfs. add( identifier( ) + "atmostone", belief( bel_def, atmost,  
         type( type_func, T, { O2T } ) ));
   }

   auto un = forall( { "P", O2T },
                 lazy_implies( apply( "strict"_unchecked, { 0_db } ), 
                    implies( apply( "atleastone"_unchecked, { 0_db } ) &&
                             apply( "atmostone"_unchecked, { 0_db } ),
                           apply( 0_db, { apply( 1_db, { 0_db } ) } ))));
   un = lambda( {{ "u", type( type_func, O, { O2T } ) }}, un );

   auto tp = type( type_func, T, { type( type_func, O, { O2T } ) } );

   blfs. add( identifier( ) + "unique", belief( bel_def, un, tp ));
#endif
}


void tests::add_settheory( logic::beliefstate& blfs )
{
   using namespace logic;

   type O = type( logic::type_obj );
   type T = type( logic::type_truthval );

   type O2O = type( type_func, O, { O } );
   type O2T = type( type_func, T, { O } );

   logic::structdef setdef;
   setdef. append( identifier( ) + "setlike", type( type_func, T, { O2T } ));
   setdef. append( identifier( ) + "mat", type( type_func, O, { O2T } ));

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
   type T = type( logic::type_truthval );

   type O2O = type( type_func, O, { O } );
   type O2T = type( type_func, T, { O } );

   type Seq = type( type_unchecked, identifier( ) + "Seq" );

   blfs. append( belief( bel_decl, identifier( ) + "s1", Seq ));
   blfs. append( belief( bel_decl, identifier( ) + "s2", Seq ));

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

   blfs. append( belief( bel_form, identifier( ) + "initial", cls, { proof( ) } ));
#if 0
   cls = term( op_kleene_or, { } );
   cl_view = cls. view_kleeneprop( );
#endif
}


void tests::transformations( logic::beliefstate& blfs )
{
   std::cout << "testing clause transformations\n";

   using namespace logic;

   {
      auto X = logic::type( type_unchecked, identifier( ) + "X" );
      auto Y = logic::type( type_unchecked, identifier( ) + "Y" );

      auto p1 = apply( "p1"_unchecked, { 1_db, 0_db } );
      auto p2 = apply( "p2"_unchecked, { 1_db, 0_db } );     
      auto p3 = apply( "p3"_unchecked, { 1_db, 0_db } );
      auto p4 = apply( "p4"_unchecked, { 1_db, 0_db } );

      auto f1 = forall( {{ "y", Y }}, equiv( p1, p2 ));
      auto f2 = forall( {{ "y", Y }}, equiv( p3, p4 ));

      auto f = forall( {{ "x", X }}, equiv( f1, f2 ));
      std::cout << f << "\n";
       
      reso::namegenerators gen;
      context ctxt;

      f = reso::repl_equiv( blfs, gen, ctxt, f, 1 );
      std::cout << "nnf = " << f << "\n";
      return;  
   }

   const auto& f = blfs. getformulas( identifier( ) + "just" );
   if( f. size( ) != 1 )
      throw std::runtime_error( "cannot continue" );

   auto ind = blfs. at( f[0] ). first;
   std::cout << "trying to make clause from " << ind << "\n";

   context ctxt;
   reso::namegenerators gen;
   std::cout << "\n\n";
   auto cls = reso::nnf( ind. view_form( ). form( ), reso::pol_neg );

   std::cout << "clause is: " << cls << "\n";
 
   cls = reso::flatten( cls );
   std::cout << "flattened: " << cls << "\n";

#if 0
   logic::simplifications::logical log;
   std::cout << log << "\n";
   std::cout << "\n";

   auto S = logic::type( logic::sel_set );
   auto T = logic::type( logic::sel_truthval );
   auto B = logic::type( logic::sel_belief );

   auto a = "A"_ident;
   auto b = "B"_ident;
   auto c = "C"_ident;
   auto P = "P"_ident;
   auto Q = "Q"_ident;

   logic::term f = exists( { "x", S }, logic::term( logic::sel_appl, P, { 0_db } ));

   for( unsigned int i = 0; i < 4; ++ i )
   {
      auto f1 = log( f, 0 );
        
      std::cout << f << " ==> " << f1;

      if( f. very_equal_to( f1 ))
         std::cout << "      (result is very equal)\n";
      else
         std::cout << "\n";

      f = !f;
   } 
#endif

}

#if 0

void tests::tableau( )
{
   logic::type S = logic::sel_set;
   logic::type T = logic::sel_truthval;

   logic::tableau tab;

   std::vector< logic::term > initial;

#if 0
   initial. push_back( "a"_ident || "b"_ident ); 
   initial. push_back( ! "a"_ident || "b"_ident ); 
   initial. push_back( "a"_ident || ! "b"_ident  );
   initial. push_back( ! "a"_ident || ! "b"_ident || "c"_ident ); 
   initial. push_back( ! "c"_ident );
#endif

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

}

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
   type T = type( logic::type_truthval );
   
   type O2O = type( type_func, O, { O } );
   type O2T = type( type_func, T, { O } );
   
   type Seq = type( type_unchecked, identifier( ) + "Seq" );

   term simp = 4_db && 7_db;

   simp = term( op_implies, simp, "xxxx"_unchecked );

   simp = term( op_forall, simp, {{ "x", O }} );
   simp = term( op_exists, simp, {{ "y", T }} );

   simp = term( op_lambda, simp, { { "v0", O }, { "v1", T } } );

   std::cout << simp << "\n";

   vector_subst subst;
   subst. push( term( op_true ));
   // subst. push( simp ); 
   std::cout << subst << "\n";

   lifter lift(3);
   std::cout << lift << "\n";

   bool change = false; 
   simp. printstate( std::cout ); 
   auto simped = topdown( lift, std::move(simp), 0, change );

   std::cout << "simped = " << simped << "\n";
   simped. printstate( std::cout );
   std::cout << "change = " << change << "\n";

#if 0
   logic::equalitysystem eq( { { 0_db, 1_db } } ); 
   std::cout << eq << "\n"; 

   long unsigned int changes = 0;
   auto simp2 = topdown_sar( changes, eq, std::move(simp), 0 );

   std::cout << "simp2 = " << simp2 << "\n";
   std::cout << "changes = " << changes << "\n"; 
#endif

}

void tests::add_seq( logic::beliefstate& blfs ) 
{
   using namespace logic;
   
   // Constructing types and de-Bruijn indices: 

   type O = logic::type( logic::type_obj );
   type T = logic::type( logic::type_truthval );

   type O2O = type( type_func, O, { O } );
   type O2T = type( type_func, T, { O } );
   type OO2T = type( type_func, T, { O, O } );
   type Seq = type( type_unchecked, identifier( ) + "Seq" );

   logic::structdef structseq;
   structseq. append( identifier( ) + "0", O );
   structseq. append( identifier( ) + "succ", O2O );

   blfs. append( belief( bel_struct, identifier( ) + "Seq", structseq ));

   {
      auto tp = type( type_func, T, 
        { type( type_unchecked, identifier( ) + "Seq" ), O2T } );

      auto f1 = apply( "0"_unchecked, { 1_db } ); 
      f1 = apply( 0_db, { f1 } );

      auto f2 = implies( apply( 1_db, { 0_db } ), 
                         apply( 1_db, { apply( apply( "succ"_unchecked, { 2_db } ), { 0_db } ) } ));
      f2 = forall( {{ "x", O }}, f2 );
      
      blfs. append( belief( bel_def, identifier( ) + "isclosed", 
         lambda( { { "s", Seq }, { "P", O2T } }, f1 && f2 ), tp ));  
   }

   {
      auto form = apply( 0_db, { 1_db } );
      auto pref = apply( "isclosed"_unchecked, { 2_db, 0_db } );
      form = implies( pref, form );
      pref = apply( "strict"_unchecked, { 0_db } );
      form = lazy_implies( pref, form );
   
      form = forall( {{ "P", O2T }}, form );
      form = lambda( {{ "x", O }}, form );
      form = lambda( {{ "s", Seq }}, form ); 

      blfs. append( belief( bel_def, identifier( ) + "gen", form, 
                type( type_func, type( type_func, T, { O } ), { Seq } )));
   }

   // Next we state correctness of induction: 

   {
      auto f2 = apply( 1_db, { 0_db } );
      auto f1 = apply( apply( "gen"_unchecked, { 2_db } ), { 0_db } );
      f1 = lazy_implies( f1, f2 );
      auto form4 = forall( {{ "x", O }}, f1 );

      f2 = apply( 1_db, { apply( apply( "succ"_unchecked, { 2_db } ), { 0_db } ) } );
        // Q( s. succ(x)) 
      f2 = implies( apply( 1_db, { 0_db } ), f2 );

      f2 = lazy_implies( apply( apply( "gen"_unchecked, { 2_db } ), { 0_db } ), f2 );
      auto form3 = forall( {{ "x", O }}, f2 );


      auto form2 = apply( 0_db, { apply( "0"_unchecked, { 1_db } ) } );
      auto form1 = apply( "stricton"_unchecked, 
                     { apply( "gen"_unchecked, { 1_db } ), 0_db } ); 

      form1 = lazy_implies( form1, implies( form2, implies( form3, form4 )));
      form1 = forall( {{ "s", Seq }, { "Q", O2T }}, form1 );
      
      blfs. append( belief( bel_form, identifier( ) + "induction", form1, 
                            { proof( ), proof( ) } ) ); 
   }

   // We define a homomorphic relation:

   {
      auto f1 = apply( 0_db, { apply( "0"_unchecked, { 2_db } ),
                               apply( "0"_unchecked, { 1_db } ) } );

      auto f2 = apply( "gen"_unchecked, { 4_db, 1_db } ) &&
                apply( "gen"_unchecked, { 3_db, 0_db } );

      auto fin = apply( 2_db, { apply( "succ"_unchecked, { 4_db, 1_db } ),
                                apply( "succ"_unchecked, { 3_db, 0_db } ) } );
      
      fin = implies( apply( 2_db, { 1_db, 0_db } ), fin ); 
      fin = lazy_implies( f2, fin ); 
      fin = forall( {{ "x1", O }, { "x2", O }}, fin );

      fin = f1 && fin; 
      fin = lambda( {{ "P", OO2T }}, fin );
      fin = lambda( {{ "s1", Seq }, { "s2", Seq }}, fin );
 
      blfs. append( belief( bel_def, identifier( ) + "homrel", fin,
                type( type_func, type( type_func, T, { OO2T } ), { Seq, Seq } )));
   }

   // minhomrel( s1, s2 : Seq ) ( x1, x2 : O ) :=
   //    [ P : T(O,O) ] { stricton( prod( s1. gen, s2. gen ), P ) } 
   //        -> homrel( s1, s2, P ) -> P( x1, x2 ).
 

   {
      auto stricton =
         apply( "stricton"_unchecked,
            { apply( "prod"_unchecked, 
               { apply( "gen"_unchecked, { 4_db } ),
                 apply( "gen"_unchecked, { 3_db } ) 
               }),
             0_db });

      auto homrel = apply( "homrel"_unchecked, { 4_db, 3_db, 0_db } );

      auto body = lazy_implies( stricton, 
                     implies( homrel, 
                        apply( 0_db, { 2_db, 1_db } )));
      
      // It remains to add the quantifiers and lambdas: 

      body = forall( {{ "P", OO2T }}, body );
      body = lambda( {{ "x1", O }, { "x2", O }}, body );
      body = lambda( {{ "s1", Seq }, { "s2", Seq }}, body );

      blfs. append( belief( bel_def, identifier( ) + "minhomrel", body,
                type( type_func, OO2T, { Seq, Seq } )));

   }
 
   // [ s1, s2 : Seq ] [ x1, x2 : O ]
   // { s1. gen(x) & s2. gen(x) } -> minhomrel( s1, s2, x1, x2 ) ->
   //    ( x1 = s1.0 & x2 = s2. 0 ) |
   //    < y1, y2 : O > { s1. gen(y1) & s2. gen(y2) } &
   //      minhomrel( s1, s2, y1, y2 ) & x1 = s1.succ(y1) & x2 = s2. succ(y2)

   {
      auto e1 = ( 3_db == apply( "succ"_unchecked, { 5_db, 1_db } ) );
      auto e2 = ( 2_db == apply( "succ"_unchecked, { 4_db, 0_db } ) );

      auto e = apply( "minhomrel"_unchecked, { 5_db, 4_db, 1_db, 0_db } );
      e = e && e1 && e2;
      
      auto ex = lazy_and(
         apply( "gen"_unchecked, { 5_db, 1_db } ) &&
         apply( "gen"_unchecked, { 4_db, 0_db } ),
         e );

      ex = exists( {{ "y1", O }, { "y2", O }}, ex );
     
      // x1 = s1.0 & x2 = s2. 0:
 
      auto conj = ( 1_db == apply( "0"_unchecked, { 3_db } ) &&
                    0_db == apply( "0"_unchecked, { 2_db } ) );
     
      auto impl = implies( 
         apply( "minhomrel"_unchecked, { 3_db, 2_db, 1_db, 0_db } ),
         conj || ex ); 

      // add: s1. gen(x1) && s2. gen( x2 ) :

      impl = lazy_implies(
         apply( "gen"_unchecked, { 3_db, 1_db } ) &&
         apply( "gen"_unchecked, { 2_db, 0_db } ),
         impl );

      // It remains to add the quantifiers:

      impl = forall( {{ "x1", O }, { "x2", O }}, impl );
      impl = forall( {{ "s1", Seq }, { "s2", Seq }}, impl );

      blfs. append( belief( bel_form, identifier( ) + "just", impl,
                            { proof( ), proof( ) } ) ); 

   }
}


void tests::structural( logic::beliefstate& blfs )
{
   using namespace logic;
   
   auto prod = blfs. at( exact(0)). first;
   // std::cout << prod << "\n";

   errorstack err; 
#if 0
   context ctxt;

   type Seq = type( type_unchecked, identifier( ) + "Seq" );
   type Zig = type( type_unchecked, identifier( ) + "Zig" );
   type Zag = type( type_unchecked, identifier( ) + "Zag" );

   auto tm = apply( "0"_unchecked, { 0_db } );
   tm = apply( "succ"_unchecked, { 0_db, tm } );
   tm = prop( tm );
   tm = forall( {{ "x", Seq }}, tm );

   std::cout << tm << "\n";
   tm. printstate( std::cout );

   auto res = checkandresolve( blfs, err, ctxt, tm );

   if( res. has_value( ))
      std::cout << "type = " << res. value( ) << "\n";
   else
      std::cout << "(no type)\n";

   std::cout << err << "\n";

   std::cout << "tm after checking = " << tm << "\n";
   tm. printstate( std::cout );

   auto tm1 = apply( "0"_unchecked, { 0_db } );
   auto tm2 = apply( "succ"_unchecked, { 1_db } );
   tm = apply( "Seq"_unchecked, { tm1, tm2 } );
   
   tm = term( op_equals, 0_db, tm );

   tm = lambda( {{ "x", Seq }, { "y", Seq }}, tm );
   std::cout << "\n\n";
   std::cout << tm << "\n";

   res = checkandresolve( blfs, err, ctxt, tm );

   if( res. has_value( ))
      std::cout << "type = " << res. value( ) << "\n";
   else
      std::cout << "(no type)\n";

   std::cout << err << "\n";

   if( ctxt. size( ) > 0 )
      throw std::runtime_error( "context not restored" );
#endif

   checkandresolve( blfs, err );
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

#if 0
void tests::tokenizer( ) {
   size_t count = 0;
   parser::tokenizer t;
   parser::symbol s ( parser::symboltype::sym_EOF, std::nullopt );
   while( ( s = t. read() ). type != parser::symboltype::sym_EOF && count < 1000 ) {
      std::cout << s << std::endl;
      ++count;
   }
}


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


void tests::proofchecking( )
{
#if 0
   logic::beliefstate bel;
   add_kuratowski( bel );
   add_simple( bel );
   add_addition( bel );

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
   std::cout << "\n\n";
   pos. restore(0);
   logic::context ctxt;
   logic::uniquenamestack names;
   try
   {
      std::cout << "proof:      "; pretty::print( std::cout, names, edit. check. topterm ); std::cout << "\n";
      logic::type prooftp = edit. check. typecheck( ctxt, pos, edit. check. topterm );
      std::cout << "type : " << prooftp << "\n";
      edit. check. checksequent( ctxt, pos, edit. check. topterm ); 
   }
   catch( const logic::failure& f )
   {
      ctxt. restore( 0 );
      edit. check. print_errors( std::cout, ctxt );
   }
#endif
#endif
}


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
