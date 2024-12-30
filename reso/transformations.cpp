
#include "transformations.h"
#include "logic/counting.h"
#include "logic/replacements.h"

logic::term 
reso::nnf( logic::beliefstate& blfs, namegenerator& gen,
           logic::context& ctxt, logic::term f, const polarity pol, 
           const unsigned int eq )
{
   if( true )
   {
      std::cout << ctxt << "\n";
      std::cout << pol << ":   " << f << "\n";
      std::cout << "eq = " << eq << "\n";
   }

   // We handle the prop-cases separately in the else: 

   if( pol == pol_pos || pol == pol_neg )
   {
      switch( f. sel( ))
      {

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

      case logic::op_forall:
      case logic::op_kleene_forall:
      case logic::op_exists:
      case logic::op_kleene_exists:
         {
            auto q = f. view_quant( );

            size_t ss = ctxt. size( );
            for( size_t i = 0; i != q. size( ); ++ i )
               ctxt. append( q. var(i). pref, q. var(i). tp );

            auto res = nnf( blfs, gen, ctxt, q. body( ), pol, eq );

            logic::selector kleenequant = f. sel( );

            if( kleenequant == logic::op_forall )
               kleenequant = logic::op_kleene_forall;

            if( kleenequant == logic::op_exists )
               kleenequant = logic::op_kleene_exists;

            // Now we are a real Kleene quantifier. 

            res = logic::term( demorgan( kleenequant, pol ), res, 
                               std::initializer_list< logic::vartype > ( ));

            // Add the quantified variables/types from the original formula:

            for( size_t i = 0; i != q. size( ); ++ i )
               res. view_quant( ). push_back( q. var(i));

            ctxt. restore( ss ); 
            return res; 
         } 

      case logic::op_equals:
      case logic::op_apply:
         if( pol == pol_pos )
            return f;
         if( pol == pol_neg )
            return logic::term( logic::op_not, f ); 

         throw std::logic_error( "should never been here" );
      }
      std::cout << "reso::nnf " << f. sel( ) << "\n";
      throw std::runtime_error( "unhandled selector" ); 
   }
   else
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
reso::introduce_predicate( logic::beliefstate& blfs, 
                           namegenerator& gen,
                           logic::context& ctxt, logic::term t )
{
   std::map< size_t, size_t > freevars = count_debruijn(t);
      // In increasing order. That means that the 
      // nearest variable comes first.

   for( const auto& p : freevars )
      std::cout << p. first << " " << p. second << "\n";

   // Create the predicate:

   auto alpha = gen. create( "alpha" );

   // Create the type of alpha:

   auto T = logic::type( logic::type_truthval ); 
   auto atype = logic::type( logic::type_func, T, {} );

   logic::sparse_subst subst; 
  
   auto it = freevars. end( );
   while( it != freevars. begin( ))
   {
      -- it; 
      std::cout << ( it -> first ) << "\n";
      atype. view_func( ). push_back( ctxt. gettype( it -> first ));
   }

   std::cout << atype << "\n"; 

   // Add the declaration of alpha:

   blfs. append( logic::belief( logic::bel_decl, 
                                identifier( ) + alpha, atype ));

   std::cout << blfs << "\n"; 
}


