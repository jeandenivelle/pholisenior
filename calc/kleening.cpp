
#include "kleening.h"

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
   case logic::op_lazy_or:
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


logic::term calc::knf( const logic::term& f, polarity pol )
{
   if constexpr( false )
      std::cout << "kleening   " << f << " / " << pol << "\n";

   switch( f. sel( ))
   {
   case logic::op_false:
   case logic::op_true:
      {
         auto s = f. sel( );
         s = kleening(s);
         s = demorgan( pol, s );
         return logic::term( s, {} );  
      }

   case logic::op_error:
      return logic::term( logic::op_kleene_and, 
                          std::initializer_list< logic::term > ( ));  
         // Because we can widen.
   
   case logic::op_not:
      return knf( f. view_unary( ). sub( ), - pol );

   case logic::op_prop:
      return knf_prop( f. view_unary( ). sub( ), pol );

   case logic::op_implies:
   case logic::op_lazy_implies:
      {
         auto bin = f. view_binary( ); 

         auto sub1 = knf( bin. sub1( ), - pol );
         auto sub2 = knf( bin. sub2( ), pol );

         return logic::term( demorgan( pol, logic::op_kleene_or ),
                             { sub1, sub2 } );
      }

   case logic::op_and:
   case logic::op_lazy_and:
   case logic::op_or:
   case logic::op_lazy_or:
      {
         auto bin = f. view_binary( );
         auto sub1 = knf( bin. sub1( ), pol );
         auto sub2 = knf( bin. sub2( ), pol );

         auto kleenop = kleening( f. sel( ));
         return logic::term( demorgan( pol, kleenop ), { sub1, sub2 } );   
      } 

   case logic::op_forall:
   case logic::op_kleene_forall:
   case logic::op_exists:
   case logic::op_kleene_exists:
      {
         auto q = f. view_quant( );
         auto body = knf( q. body( ), pol );
         
         body = logic::term( demorgan( pol, kleening( f. sel( )) ), body, 
                             std::initializer_list< logic::vartype > ( ));

         // Add the quantified variables+types from the original formula:

         for( size_t i = 0; i != q. size( ); ++ i )
            body. view_quant( ). push_back( q. var(i));

         return body; 
      } 

   case logic::op_equiv:
      {
         auto eq = f. view_binary( );
        
         auto A = knf( eq. sub1( ), pol );
         auto negA = knf( eq. sub1( ), -pol );

         auto B = knf( eq. sub2( ), pol );
         auto negB = knf( eq. sub2( ), -pol );
 
         using namespace logic;

            // In case of negative polarity, we could also return
            // ( A \/ B ) /\ ( !A \/ !B ), but that seems harder
            // to handle.

         return term( demorgan( pol, op_kleene_and ),
            { term( demorgan( pol, op_kleene_or ), { negA, B } ),
              term( demorgan( pol, op_kleene_or ), { A, negB } ) } );
      }
   
   case logic::op_kleene_or:
   case logic::op_kleene_and:
      {
         auto res = logic::term( demorgan( pol, f. sel( )),
                                 std::initializer_list< logic::term > ( ));
         
         auto kln1 = f. view_kleene( );
         auto kln2 = res. view_kleene( );
         for( size_t i = 0; i != kln1. size( ); ++ i )
            kln2. push_back( knf( kln1. sub(i), pol ));
         return res;
      }
   case logic::op_exact:
   case logic::op_debruijn:
   case logic::op_unchecked:
   case logic::op_equals:
   case logic::op_lambda:
   case logic::op_apply:
      if( pol == pol_pos )
         return f;
      else
         return logic::term( logic::op_not, f );
   }
   std::cout << "knf " << pol << " : " << f. sel( ) << "\n";
   throw std::runtime_error( "operator not implemented" );
}

logic::term
calc::knf_prop( const logic::term& f, polarity pol )
{
   if constexpr( true )
      std::cout << "knf-prop: " << f << " / " << pol << "\n";

   switch( f. sel( ))
   {
    
#if 0
   {
      // Cases for # or !# : 

#endif 
   case logic::op_and:
   case logic::op_or:
   case logic::op_implies:
   case logic::op_equiv:
      {
         auto strct = f. view_binary( ); 

         auto sub1 = knf_prop( strct. sub1( ), pol );
         auto sub2 = knf_prop( strct. sub2( ), pol );
         return logic::term( demorgan( pol, logic::op_kleene_and ),
                             { sub1, sub2 } );
      }
#if 0
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
#endif 

   case logic::op_forall:
   case logic::op_exists:
      {
         auto q = f. view_quant( );

         auto res = knf_prop( q. body( ), pol );

         res = logic::term( demorgan( pol, logic::op_kleene_forall ), 
                            res,
                            std::initializer_list< logic::vartype > ( ));

            // Add the quantified variables/types from the original formula:

         for( size_t i = 0; i != q. size( ); ++ i )
            res. view_quant( ). push_back( q. var(i));

         return res; 
      }

   case logic::op_exact:
   case logic::op_debruijn:
   case logic::op_unchecked: 
   case logic::op_apply:
      if( pol == pol_pos )
         return logic::term( logic::op_prop, f );
      else
      {
         return logic::term( logic::op_not,
                   logic::term( logic::op_prop, f ));
      }

   }
   std::cout << pol << " : " << f. sel( ) << "\n";
   throw std::runtime_error( "not handled in knf-prop" );
}

