
#include "transformations.h"
#include "logic/counting.h"
#include "logic/replacements.h"


bool reso::issimple( const logic::term& f )
{
   return false;

   switch( f. sel( ))
   {
   case logic::op_exact:
   case logic::op_debruijn:
   case logic::op_unchecked:
   case logic::op_false:
   case logic::op_error:
   case logic::op_true:
      return true;

   case logic::op_and:
   case logic::op_or:
   case logic::op_implies:
   case logic::op_equiv:
   case logic::op_lazy_and:
   case logic::op_lazy_or:
   case logic::op_lazy_implies:
      return false;

   case logic::op_forall:
   case logic::op_exists:
   case logic::op_kleene_forall:
   case logic::op_kleene_exists:
      return issimple( f. view_quant( ). body( ));  

   case logic::op_equals:
   case logic::op_apply:
      return true;
   }

   std::cout << "\n";
   std::cout << f. sel( ) << "\n";
   throw std::logic_error( "size_upto: selector not handled" ); 
}


logic::term
reso::repl_equiv( logic::beliefstate& blfs, namegenerators& gen,
                  logic::context& ctxt, logic::term f, unsigned int maxequiv )
{
   std::cout << "replace_equiv: " << f << " / " << maxequiv << "\n";

   switch( f. sel( ))
   {

   case logic::op_forall:
   case logic::op_exists:
   case logic::op_kleene_forall:
   case logic::op_kleene_exists:
      {
         auto q = f. view_quant( );
         size_t ss = ctxt. size( );

         for( size_t i = 0; i != q. size( ); ++ i ) 
            ctxt. append( q. var(i). pref, q. var(i). tp );

         q. update_body( 
               repl_equiv( blfs, gen, ctxt, q. extr_body( ), maxequiv ));

          ctxt. restore( ss );
      } 
      return f;

   case logic::op_equiv:
      {
         auto eqv = f. view_binary( );
         if( maxequiv == 0 &&
             ( !issimple( eqv. sub1( )) || !issimple( eqv. sub2( )) ))
         {
            std::cout << ctxt << "\n";

            f = repl_subform( blfs, gen, ctxt, f, true );
            return f;
         }

         if( maxequiv > 0 )
            -- maxequiv;

         eqv. update_sub1( 
                 repl_equiv( blfs, gen, ctxt, eqv. extr_sub1( ), maxequiv ));
         eqv. update_sub2( 
                 repl_equiv( blfs, gen, ctxt, eqv. extr_sub2( ), maxequiv ));
      }
      return f;

   case logic::op_apply:
      return f;
   } 

   std::cout << "not defined " << f. sel( ) << "\n";
   throw std::runtime_error( "replace equivs" );
}


logic::term reso::nnf( logic::term f, polarity pol )
{
   if( true )
      std::cout << pol << ":   " << f << "\n";

   switch( f. sel( ))
   {
   
#if 0
      case logic::op_implies:
      case logic::op_lazy_implies:
         {
            auto bin = f. view_binary( ); 

            auto sub1 = nnf( blfs, gen, ctxt, bin. sub1( ), negate( pol ), eq );
            auto sub2 = nnf( blfs, gen, ctxt, bin. sub2( ), pol, eq );

            return logic::term( demorgan( logic::op_kleene_or, pol ),
                                { sub1, sub2 } );
         }

      case logic::op_and:
      case logic::op_or:
      case logic::op_lazy_and:
         {
            auto bin = f. view_binary( );
            auto sub1 = nnf( blfs, gen, ctxt, bin. sub1( ), pol, eq );
            auto sub2 = nnf( blfs, gen, ctxt, bin. sub2( ), pol, eq );

            auto kleenop = f. sel( );
            if( f. sel( ) == logic::op_and )
               kleenop = logic::op_kleene_and;
            if( f. sel( ) == logic::op_or )
               kleenop = logic::op_kleene_or;
            if( f. sel( ) == logic::op_lazy_and )
               kleenop = logic::op_kleene_and;

            return logic::term( demorgan( kleenop, pol ), { sub1, sub2 } );   
         } 
#endif
   case logic::op_forall:
   case logic::op_kleene_forall:
   case logic::op_exists:
   case logic::op_kleene_exists:
      {
         auto q = f. view_quant( );

         auto res = nnf( q. body( ), pol );

         logic::selector kleenequant = f. sel( );

         if( kleenequant == logic::op_forall )
            kleenequant = logic::op_kleene_forall;

         if( kleenequant == logic::op_exists )
            kleenequant = logic::op_kleene_exists;

         // Now we are a real Kleene quantifier. 

         res = logic::term( demorgan( pol, kleenequant ), res, 
                            std::initializer_list< logic::vartype > ( ));

         // Add the quantified variables/types from the original formula:

         for( size_t i = 0; i != q. size( ); ++ i )
            res. view_quant( ). push_back( q. var(i));

         return res; 
      } 

   case logic::op_equiv:
      {
         auto eq = f. view_binary( );
         
         auto A = nnf( eq. sub1( ), pol );
         auto negA = nnf( eq. sub1( ), -pol );

         auto B = nnf( eq. sub2( ), pol );
         auto negB = nnf( eq. sub2( ), -pol );
 
         using namespace logic;

         return term( demorgan( pol, op_kleene_and ),
            { term( demorgan( pol, op_kleene_or ), { negA, B } ),
              term( demorgan( pol, op_kleene_or ), { negB, A } ) } );
      }

   case logic::op_exact:
   case logic::op_debruijn:
   case logic::op_unchecked:
   case logic::op_false:
   case logic::op_error:
   case logic::op_true:

   case logic::op_equals:
   case logic::op_apply:
      if( pol == pol_pos )
         return f;
      if( pol == pol_neg )
         return logic::term( logic::op_not, f ); 
   }

   std::cout << "nnf " << pol << " : " << f. sel( ) << "\n";
   throw std::runtime_error( "operator not implemented" );
}


#if 0
   {
      // Cases for # or !# : 
 
      switch( f. sel( ))
      {

      case logic::op_and:
      case logic::op_or:
      case logic::op_implies:
      case logic::op_equiv:
         {
            auto eager = f. view_binary( ); 

            auto sub1 = nnf( blfs, gen, ctxt, eager. sub1( ), pol, eq );
            auto sub2 = nnf( blfs, gen, ctxt, eager. sub2( ), pol, eq );
            return logic::term( demorgan( logic::op_kleene_and, pol ),
                                { sub1, sub2 } );
         }

      case logic::op_lazy_and:
      case logic::op_lazy_or:
      case logic::op_lazy_implies:
         {
            auto lazy = f. view_binary( ); 
            auto sub1prop = nnf( blfs, gen, ctxt, lazy. sub1( ), pol, eq );
            std::cout << sub1prop << "\n"; 
           
            polarity sub1pol = ( f. sel( ) == logic::op_lazy_and || 
                                 f. sel( ) == logic::op_lazy_implies ) ? 
                           pol_neg : pol_pos;

            if( pol == pol_negprop )
               sub1pol = negate( sub1pol );

            std::cout << sub1pol << "\n";
            auto sub1 = nnf( blfs, gen, ctxt, lazy.sub1( ), sub1pol, eq );
            std::cout << sub1 << "\n";

            auto sub2prop = nnf( blfs, gen, ctxt, lazy. sub2( ), pol, eq );
            std::cout << sub2prop << "\n";

            return logic::term( demorgan( logic::op_kleene_and, pol ),
                { sub1prop, logic::term( demorgan( logic::op_kleene_or, pol ), 
                     { sub1, sub2prop } ) } ); 
         }

      case logic::op_forall:
      case logic::op_exists:
         {
            auto q = f. view_quant( );

            size_t ss = ctxt. size( );
            for( size_t i = 0; i != q. size( ); ++ i )
               ctxt. append( q. var(i). pref, q. var(i). tp );

            auto res = nnf( blfs, gen, ctxt, q. body( ), pol, eq );

            res = logic::term( demorgan( logic::op_kleene_forall, pol ), 
                               res,
                               std::initializer_list< logic::vartype > ( ));

            // Add the quantified variables/types from the original formula:

            for( size_t i = 0; i != q. size( ); ++ i )
               res. view_quant( ). push_back( q. var(i));

            ctxt. restore( ss );

            return res; 
         }

      case logic::op_apply:
         if( pol == pol_prop )
            return logic::term( logic::op_prop, f );

         if( pol == pol_negprop )
         {
            return logic::term( logic::op_not,
                      logic::term( logic::op_prop, f ));
         }

         throw std::logic_error( "should not have been here" );
      }
      std::cout << pol << " : " << f. sel( ) << "\n";
      throw std::runtime_error( "prop not handled" );
   }
}

#endif

namespace
{
  
   void flatten_disj( std::vector< logic::term > & res,
                      logic::context& ctxt, logic::term f )
   {
      std::cout << ctxt << "\n";
      std::cout << "flatten_disj: " << f << "\n";

      if( f. sel( ) == logic::op_kleene_exists )
      {
         auto ex = f. view_quant( );
         size_t csize = ctxt. size( );
         for( size_t i = 0; i != ex. size( ); ++ i )
            ctxt. append( ex. var(i). pref, ex. var(i). tp );  
         flatten_disj( res, ctxt, ex. body( ));
         ctxt. restore( csize );  
         return; 
      }

      if( f. sel( ) == logic::op_kleene_or )
      {
         auto kl = f. view_kleene( );
         for( size_t i = 0; i != kl. size( ); ++ i )
            flatten_disj( res, ctxt, kl. sub(i));
         return;
      }

      f = reso::flatten( std::move(f)); 

      if( ctxt. size( ) > 0 )
      {
         f = logic::term( logic::op_kleene_exists, f, 
                          std::initializer_list< logic::vartype > ( ));
         size_t ind = ctxt. size( );
         while( ind )
         {
            -- ind;
            f. view_quant( ). push_back( logic::vartype( ctxt. getname( ind ),
                                                 ctxt. gettype( ind ))); 
         } 
      }

      res. push_back( std::move(f) );
   }
                    

   void flatten_conj( std::vector< logic::term > & res,
                      logic::context& ctxt, logic::term f )
   {
      std::cout << ctxt << "\n";
      std::cout << "flatten_conj: " << f << "\n";

      if( f. sel( ) == logic::op_kleene_forall )
      {
         auto ex = f. view_quant( );
         size_t csize = ctxt. size( );
         for( size_t i = 0; i != ex. size( ); ++ i )
            ctxt. append( ex. var(i). pref, ex. var(i). tp );
         flatten_conj( res, ctxt, ex. body( ));
         ctxt. restore( csize );
         return;  
      }

      if( f. sel( ) == logic::op_kleene_and )
      {
         auto kl = f. view_kleene( );
         for( size_t i = 0; i != kl. size( ); ++ i ) 
            flatten_conj( res, ctxt, kl. sub(i));
         return; 
      }

      f = reso::flatten( std::move(f));

      if( ctxt. size( ) > 0 )
      {
         f = logic::term( logic::op_kleene_forall, f,
                          std::initializer_list< logic::vartype > ( ));
         size_t ind = ctxt. size( );
         while( ind )
         {
            -- ind;
            f. view_quant( ). push_back( logic::vartype( ctxt. getname( ind ),
                                                 ctxt. gettype( ind )));
         }
      }

      res. push_back( std::move(f) );
   }
   
}


logic::term
reso::flatten( logic::term f )
{
   switch( f. sel( ))
   {
   case logic::op_kleene_or:
   case logic::op_kleene_exists:
      {
         std::vector< logic::term > disj;
         logic::context ctxt;
         flatten_disj( disj, ctxt, f );
 
         // If the resulting disjunction contains only
         // one element, we don't build it.
         // Not sure if this should be done.

         if( disj. size( ) == 1 )
            return disj. front( );
         else
            return logic::term( logic::op_kleene_or, 
                                disj. begin( ), disj. end( )); 
      }   

   case logic::op_kleene_and:
   case logic::op_kleene_forall:
      {
         std::vector< logic::term > conj;
         logic::context ctxt;
         flatten_conj( conj, ctxt, f );
         if( conj. size( ) == 1 )
            return conj. front( );
         else
            return logic::term( logic::op_kleene_and,
                                conj. begin( ), conj. end( )); 
      }

   case logic::op_apply:
   case logic::op_equals:
   case logic::op_not:
      return f;
   }

   throw std::runtime_error( "cannot handle" ); 
}


logic::term
reso::repl_subform( logic::beliefstate& blfs, 
                    namegenerators& gen,
                    logic::context& ctxt, logic::term ff, bool equiv )
{
   auto freevars = count_debruijn( ff );
      // In increasing order. That means that the 
      // nearest variable comes first.

   std::cout << freevars << "\n";

   // Create the new predicate:

   identifier pred = identifier( ) + gen. pred. next( );

   while( blfs. getfunctions( pred ). size( ) ||
          blfs. getstructdefs( pred ). size( ))
   {
      pred = identifier( ) + gen. predisprop. next( );
   }
 
   // Create the type of pred:

   auto T = logic::type( logic::type_truthval ); 
   auto atype = logic::type( logic::type_func, T, {} );

   logic::sparse_subst subst; 
  
   for( auto it = freevars. end( ); it != freevars. begin( ); )
   {
      -- it; 
      atype. view_func( ). push_back( ctxt. gettype( it -> first ));
   }

   std::cout << atype << "\n"; 

   // Add the declaration of pred:

   blfs. append( logic::belief( logic::bel_decl, pred, atype ));

   // Create forall( x1, ..., xn ) # pred( x1, ..., xn ) :

   auto atom = logic::term( logic::op_unchecked, pred );
   atom = logic::term( logic::op_apply, atom, 
                       std::initializer_list< logic::term > ( ));

   std::cout << "atom = " << atom << "\n";

   for( size_t i = freevars. size( ); i; )
   {
      -- i;
      atom. view_apply( ). push_back( logic::term( logic::op_debruijn, i ));
   }

   auto forall = logic::term( logic::op_kleene_forall, 
                       logic::term( logic::op_prop, atom ),
                       std::initializer_list< logic::vartype > ( ));

   for( auto it = freevars. end( ); it != freevars. begin( ); )
   {
      -- it;
      forall. view_quant( ). push_back( { "xx", ctxt. gettype( it -> first ) } );
   }

   blfs. append( logic::belief( logic::bel_form, identifier( ) + 
                 gen. predisprop. next( ), forall, { } ));

   logic::sparse_subst norm;
   {
      auto it = freevars. begin( );
      size_t var = 0;
      while( it != freevars. end( ))
      {
         norm. assign( it -> first, logic::term( logic::op_debruijn, var )); 
         ++ it; ++ var;
      }
   }

   std::cout << "norm = " << norm << "\n";

   bool change = false; 
   ff = topdown( norm, std::move( ff ), 0, change );

   forall. view_quant( ). update_body( 
      logic::term( logic::op_kleene_or, {
         logic::term( logic::op_not, atom ), ff } ));
     
   blfs. append( logic::belief( logic::bel_form, identifier( ) +
                 gen. preddef. next( ), forall, { } ));

   atom = logic::term( logic::op_apply, 
                       logic::term( logic::op_unchecked, pred ),
                       std::initializer_list< logic::term > ( ));

   for( auto it = freevars. end( ); it != freevars. begin( ); )
   {
      -- it;
      atom. view_apply( ). push_back( logic::term( logic::op_debruijn, it -> first ));
   }
 
   std::cout << blfs << "\n"; 
   std::cout << "the atom is " << atom << "\n";
   return ff;
}


