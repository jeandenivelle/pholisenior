
#include "splitequiv.h"
#include "util.h"

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

            auto pr = norm_debruijns(f);
            std::cout << pr. first << "\n"; 
            std::cout << "normalized subform: " << pr. second << "\n"; 

            std::cout << "original context " << ctxt << "\n";
            auto restr = restriction( ctxt, pr. first ); 
               // ctxt, restricted to the variables that occur
               // in pr. second.

            std::cout << restr << "\n";
 
            logic::exact pred = trans. newpredsym( blfs, "equiv", restr );

            trans. push( std::move( restr ), pred, pr. second,
                         pol_neg, step_splitequiv );

            restr = restriction( ctxt, pr. first );
               // We need to recreate restr, because the original
               // restr was moved into trans. 
 
            trans. push( std::move( restr ), pred, 
                         logic::term( logic::op_not, pr. second ),
                         pol_pos, step_splitequiv );

            auto appl = application( 
               logic::term( logic::op_exact, pred ), pr. first );
            std::cout << "should we return?\n";
            throw std::logic_error( "what" );
         }
      }
   case logic::op_apply:
   case logic::op_equals:
      return f;
   } 
   std::cout << "not defined for: " << f. sel( ) << "\n";
   throw std::runtime_error( "remove equiv" );
}


