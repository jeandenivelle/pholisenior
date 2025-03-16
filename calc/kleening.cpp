
#include "kleening.h"

logic::selector calc::kleening( logic::selector op )
{
   using namespace logic;

   switch( op )
   {
   case op_false:
      return op_kleene_or;
   case op_true:
      return op_kleene_and;

   case op_and:
   case op_lazy_and:
      return op_kleene_and;

   case op_or:
   case op_lazy_or:
      return op_kleene_or; 

   case op_forall:
   case op_kleene_forall:
      return op_kleene_forall;

   case op_exists:
   case op_kleene_exists: 
      return op_kleene_exists;
   }
  
   std::cout << "kleening not implemented for " << op << "\n";
   throw std::runtime_error( "not implemented" ); 
}


logic::term calc::knf( const logic::term& f, polarity pol )
{
   if constexpr( false )
      std::cout << "kleening   " << f << " / " << pol << "\n";

   using namespace logic;

   switch( f. sel( ))
   {
   case op_false:
   case op_true:
      {
         auto s = f. sel( );
         s = kleening(s);
         s = demorgan( pol, s );
         return term( s, {} );  
      }

   case op_error:
      return term( op_kleene_and, std::initializer_list< term > ( ));  
         // Because we can widen.
   
   case op_not:
      return knf( f. view_unary( ). sub( ), - pol );

   case op_prop:
      return knf_prop( f. view_unary( ). sub( ), pol );

   case op_implies:
   case op_lazy_implies:
      {
         auto bin = f. view_binary( ); 

         auto sub1 = knf( bin. sub1( ), - pol );
         auto sub2 = knf( bin. sub2( ), pol );

         return term( demorgan( pol, op_kleene_or ),
                             { sub1, sub2 } );
      }

   case op_and:
   case op_lazy_and:
   case op_or:
   case op_lazy_or:
      {
         auto bin = f. view_binary( );
         auto sub1 = knf( bin. sub1( ), pol );
         auto sub2 = knf( bin. sub2( ), pol );

         auto kleenop = kleening( f. sel( ));
         return term( demorgan( pol, kleenop ), { sub1, sub2 } );   
      } 

   case op_forall:
   case op_kleene_forall:
   case op_exists:
   case op_kleene_exists:
      {
         auto q = f. view_quant( );
         auto body = knf( q. body( ), pol );
         
         body = term( demorgan( pol, kleening( f. sel( )) ), body, 
                      std::initializer_list< vartype > ( ));

         // Add the quantified variables+types from the original formula:

         for( size_t i = 0; i != q. size( ); ++ i )
            body. view_quant( ). push_back( q. var(i));

         return body; 
      } 

   case op_equiv:
      {
         auto eq = f. view_binary( );
        
         auto A = knf( eq. sub1( ), pol );
         auto negA = knf( eq. sub1( ), -pol );

         auto B = knf( eq. sub2( ), pol );
         auto negB = knf( eq. sub2( ), -pol );
 
            // In case of negative polarity, we could also return
            // ( A \/ B ) /\ ( !A \/ !B ), but that seems harder
            // to handle.

         return term( demorgan( pol, op_kleene_and ),
            { term( demorgan( pol, op_kleene_or ), { negA, B } ),
              term( demorgan( pol, op_kleene_or ), { A, negB } ) } );
      }
   
   case op_kleene_or:
   case op_kleene_and:
      {
         auto res = term( demorgan( pol, f. sel( )),
                          std::initializer_list< term > ( ));
         
         auto kln1 = f. view_kleene( );
         auto kln2 = res. view_kleene( );
         for( size_t i = 0; i != kln1. size( ); ++ i )
            kln2. push_back( knf( kln1. sub(i), pol ));
         return res;
      }

   case op_exact:
   case op_debruijn:
   case op_unchecked:
   case op_equals:
   case op_lambda:
   case op_apply:
      if( pol == pol_pos )
         return f;
      else
         return term( op_not, f );
   }
   std::cout << "knf " << pol << " : " << f. sel( ) << "\n";
   throw std::runtime_error( "operator not implemented" );
}

logic::term
calc::knf_prop( const logic::term& f, polarity pol )
{
   if constexpr( true )
      std::cout << "knf-prop: " << f << " / " << pol << "\n";

   using namespace logic;

   switch( f. sel( ))
   {
   case op_true:
   case op_false:
      return term( demorgan( pol, op_kleene_and ),
                   std::initializer_list< term > ( ));

   case op_error:
      return term( demorgan( pol, op_kleene_or ),
                   std::initializer_list< term > ( )); 

   case op_not:
      return knf_prop( f. view_unary( ). sub( ), pol );

   case op_prop:
      return term( demorgan( pol, op_kleene_and ),
                   std::initializer_list< term > ( ));

   case op_and:
   case op_or:
   case op_implies:
   case op_equiv:
      {
         auto strct = f. view_binary( ); 

         auto sub1 = knf_prop( strct. sub1( ), pol );
         auto sub2 = knf_prop( strct. sub2( ), pol );
         return term( demorgan( pol, op_kleene_and ), { sub1, sub2 } );
      }

   case logic::op_lazy_and:
   case logic::op_lazy_or:
   case logic::op_lazy_implies:
      {
         auto lazy = f. view_binary( ); 
         auto sub1prop = knf_prop( lazy. sub1( ), pol );
         
         auto sub1pol = pol;
         if( f. sel( ) == op_lazy_and || f. sel( ) == op_lazy_implies )
            sub1pol = - sub1pol;   

         auto sub1 = knf( lazy.sub1( ), sub1pol );
         auto sub2prop = knf_prop( lazy. sub2( ), pol );

         return term( demorgan( pol, logic::op_kleene_and ),
             { sub1prop, term( demorgan( pol, op_kleene_or ), 
                  { sub1, sub2prop } ) } ); 
      }

   case op_forall:
   case op_exists:
      {
         auto q = f. view_quant( );

         auto res = knf_prop( q. body( ), pol );

         res = term( demorgan( pol, op_kleene_forall ), 
                     res, std::initializer_list< vartype > ( ));

            // Add the quantified variables/types from the original formula:

         for( size_t i = 0; i != q. size( ); ++ i )
            res. view_quant( ). push_back( q. var(i));

         return res; 
      }

   case op_exact:
   case op_debruijn:
   case op_unchecked: 
   case op_apply:
      if( pol == pol_pos )
         return term( op_prop, f );
      else
         return term( op_not, term( op_prop, f ));

   }
   std::cout << pol << " : " << f. sel( ) << "\n";
   throw std::runtime_error( "not handled in knf-prop" );
}

