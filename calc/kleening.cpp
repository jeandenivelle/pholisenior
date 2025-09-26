
#include "kleening.h"

logic::selector calc::kleenop( logic::selector op )
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

   std::cout << "kleenop not implemented for " << op << "\n";
   throw std::runtime_error( "kleenop not implemented" );
}

logic::term calc::apply( const logic::term& f, polarity pol )
{
   switch( pol )
   {
   case pol_pos: 
      return f;
   case pol_neg: 
      if( f. sel( ) == logic::op_not )
         return f. view_unary( ). sub( );
      else
         return logic::term( logic::op_not, f );
   }
   std::cout << pol << "\n";
   throw std::logic_error( "cannot apply unknown polarity" ); 
}

logic::term calc::apply_prop( const logic::term& f, polarity pol )
{
   if( f. sel( ) == logic::op_not )
      return apply_prop( f. view_unary( ). sub( ), pol );

   switch( pol )
   {
   case pol_pos:
      return logic::term( logic::op_prop, f ); 
   case pol_neg:
      return logic::term( logic::op_not, logic::term( logic::op_prop, f ));
   }
   std::cout << pol << "\n";
   throw std::logic_error( "cannot apply unknown polarity" );
}

logic::term calc::kleene_top( const logic::term& f, polarity pol )
{
   if constexpr( false )
      std::cout << "kleene top : " << f << " / " << pol << "\n\n";

   using namespace logic;

   switch( f. sel( ))
   {
   case op_false:
   case op_true:
      {
         auto s = f. sel( );
         s = kleenop(s);
         s = demorgan( pol, s );
         return term( s, {} );
      }

   case op_not:
      return kleene_top( f. view_unary( ). sub( ), -pol );

   case op_prop:
      return kleene_top_prop( f. view_unary( ). sub( ), pol );

   case op_implies:
   case op_lazy_implies:
      {
         auto bin = f. view_binary( );

         auto sub1 = apply( bin. sub1( ), - pol );
         auto sub2 = apply( bin. sub2( ), pol );

         return term( demorgan( pol, op_kleene_or ), { sub1, sub2 } );
      }

   case op_and:
   case op_or:
   case op_lazy_and:
   case op_lazy_or:
      {
         auto bin = f. view_binary( );
         auto sub1 = apply( bin. sub1( ), pol );
         auto sub2 = apply( bin. sub2( ), pol );

         auto op = kleenop( f. sel( ));
         return term( demorgan( pol, op ), { sub1, sub2 } );
      }

   case op_kleene_and:
   case op_kleene_or: 
      {
         auto kl = f. view_kleene( );
         if( kl. size( ) == 1 )
            return kleene_top( kl. sub(0), pol );

         if( pol == pol_neg )
         {
            throw 
            std::logic_error( "kleene top: Kleene operator must be positive" );
         }

         return f;
      }

   case op_forall:
   case op_kleene_forall:
   case op_exists:
   case op_kleene_exists:
      {
         auto q = f. view_quant( );
         auto body = apply( q. body( ), pol );

         body = term( demorgan( pol, kleenop( f. sel( )) ), body,
                      std::initializer_list< vartype > ( ));

         // Add the quantified variables+types from the original formula:

         for( size_t i = 0; i != q. size( ); ++ i )
            body. view_quant( ). push_back( q. var(i));

         return body;
      }

  case op_equiv:
      {
         auto eqv = f. view_binary( );
         auto sub1 = eqv. sub1( );
         auto sub2 = eqv. sub2( );

         switch( pol )
         {
         case pol_pos:
            return logic::term( op_kleene_and,
                { term( op_or, apply( sub1, pol_neg ), sub2 ),
                  term( op_or, apply( sub2, pol_neg ), sub1 ) } ); 
         case pol_neg:
            return logic::term( op_kleene_or,
                { term( op_and, sub1, apply( sub2, pol_neg )),
                  term( op_and, sub2, apply( sub1, pol_neg )) } );
         } 
         std::cout << pol << "\n";
         throw std::logic_error( "unknown polarity for kleene equiv" );  
      }

   case op_exact:
   case op_debruijn:
   case op_unchecked:
   case op_equals:
   case op_apply:
      return apply( f, pol );
   }

   std::cout << "kleene top " << pol << " : " << f. sel( ) << "\n";
   throw std::runtime_error( "operator not implemented" );
}


logic::term calc::kleene_top_prop( const logic::term& f, polarity pol )
{
   if constexpr( false )
      std::cout << "kleene topprop : " << f << " / " << pol << "\n";

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
      return kleene_top_prop( f. view_unary( ). sub( ), pol );

   case op_prop:
   case op_equals:
      return term( demorgan( pol, op_kleene_and ),
                   std::initializer_list< term > ( ));

   case op_and:
   case op_or:
   case op_implies:
   case op_equiv:
      {
         auto bin = f. view_binary( );

         auto sub1 = apply_prop( bin. sub1( ), pol );
         auto sub2 = apply_prop( bin. sub2( ), pol );
         return term( demorgan( pol, op_kleene_and ), { sub1, sub2 } );
      }

   case logic::op_lazy_and:
   case logic::op_lazy_or:
   case logic::op_lazy_implies:
      {
         auto lazy = f. view_binary( );
         auto sub1prop = apply_prop( lazy. sub1( ), pol );

         auto sub1pol = pol;
         if( f. sel( ) == op_lazy_and || f. sel( ) == op_lazy_implies )
            sub1pol = -sub1pol;

         auto sub1 = apply( lazy.sub1( ), sub1pol );
         auto sub2prop = apply_prop( lazy. sub2( ), pol );
 
         switch( pol )
         {
         case pol_pos:
            return term( op_kleene_and,
                      { sub1prop, term( op_or, sub1, sub2prop ) } );

         case pol_neg:
            return term( op_kleene_or,
                      { sub1prop, term( op_and, sub1, sub2prop ) } );
         }
         std::cout << pol << "\n";
         throw std::logic_error( "unknown polarity in lazy prop-kleene" );
      }

   case op_forall:
   case op_exists:
      {
         auto q = f. view_quant( );

         auto res = apply_prop( q. body( ), pol );

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
      return apply_prop( f, pol );
   }

   std::cout << "kleene top prop " << pol << " : " << f. sel( ) << "\n";
   throw std::runtime_error( "operator not implemented" );
}


