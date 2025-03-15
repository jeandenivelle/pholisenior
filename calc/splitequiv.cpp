
#include "splitequiv.h"

logic::term
calc::splitequiv( transformer& trans, logic::beliefstate& blfs, 
                  logic::context& ctxt, logic::term f, 
                  unsigned int nrequiv )
{
   // std::cout << "split equiv: " << f << " / " << nrequiv << "\n";

   switch( f. sel( ))
   {
   case logic::op_debruijn:
   case logic::op_exact:
   case logic::op_unchecked: 
   case logic::op_false: 
   case logic::op_error:
   case logic::op_true:
      return f;
 
   case logic::op_not: 
   case logic::op_prop:
      {
         auto un = f. view_unary( );
         un. update_sub( 
            splitequiv( trans, blfs, ctxt, un. extr_sub( ), nrequiv ));
         return f;
      }
 
   case logic::op_and:
   case logic::op_or:
   case logic::op_implies:
   case logic::op_lazy_and:
   case logic::op_lazy_or:
   case logic::op_lazy_implies:
      {
         auto bin = f. view_binary( );
         bin. update_sub1( 
                splitequiv( trans, blfs, ctxt, bin. extr_sub1( ), nrequiv ));
         bin. update_sub2(
                splitequiv( trans, blfs, ctxt, bin. extr_sub2( ), nrequiv ));
         return f;
      }

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
               splitequiv( trans, blfs, ctxt, q. extr_body( ), nrequiv ));

          ctxt. restore( ss );
          return f;
      } 

   case logic::op_equiv:
      {
         auto eqv = f. view_binary( );
         if( nrequiv < maxequivs )
         {
            eqv. update_sub1(
                splitequiv( trans, blfs, ctxt, eqv. extr_sub1( ), nrequiv+1 ));
            eqv. update_sub2(
                splitequiv( trans, blfs, ctxt, eqv. extr_sub2( ), nrequiv+1 ));
            return f;
         }
         else
         {
            eqv. update_sub1(
                splitequiv( trans, blfs, ctxt, eqv. extr_sub1( ), 1 ));
            eqv. update_sub2(
                splitequiv( trans, blfs, ctxt, eqv. extr_sub2( ), 1 ));

            auto pr = trans. extractsubform( blfs, "equiv", ctxt,  f );
            std::cout << "atom: " << pr. first << "\n";
            std::cout << "normalized subform: " << pr. second << "\n"; 
            logic::exact pred = pr. first. view_apply( ). func( ). 
                                           view_exact( ). ex( );

            trans. push( pred, pr. second,
                         pol_neg, step_splitequiv );
            trans. push( pred, logic::term( logic::op_not, pr. second ),
                         pol_pos, step_splitequiv );

            return pr. first;  
         }
      }
   case logic::op_apply:
   case logic::op_equals:
      return f;
   } 
   std::cout << "not defined for: " << f. sel( ) << "\n";
   throw std::runtime_error( "remove equiv" );
}


#if 0
logic::selector calc::kleening( logic::selector op )
{
   switch( op )
   {
   case logic::op_false:
      return logic::op_kleene_or;
   case logic::op_true:
      return logic::op_kleene_and;

   case logic::op_and:
   case logic::op_lazy_and:
      return logic::op_kleene_and;

   case logic::op_or:
      return logic::op_kleene_or; 

   case logic::op_forall:
   case logic::op_kleene_forall:
      return logic::op_kleene_forall;

   case logic::op_exists:
   case logic::op_kleene_exists: 
      return logic::op_kleene_exists;

   }
  
   std::cout << "kleening not implemented for " << op << "\n";
   throw std::runtime_error( "not implemented" ); 
}


#endif
#if 0
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
#endif

