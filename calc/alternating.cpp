
#include "alternating.h"
#include "kleening.h"
#include "util.h"

logic::selector
calc::quantof( logic::selector op )
{
   if( op == logic::op_kleene_and )
      return logic::op_kleene_forall;
   if( op == logic::op_kleene_or )
      return logic::op_kleene_exists;
   std::cout << op << "\n";
   throw std::logic_error( "quantof: not a Kleene connective" );
}

logic::selector
calc::alternation( logic::selector op )
{
   if( op == logic::op_kleene_and )
      return logic::op_kleene_or;
   if( op == logic::op_kleene_or )
      return logic::op_kleene_and;
   std::cout << op << "\n";
   throw std::logic_error( "alternation: not a Kleene connective" );
}

logic::term 
calc::alternating( const logic::term& f, logic::selector op, 
                   unsigned int rank ) 
{
   if constexpr( false )
   {
      std::cout << "alternating " << op << "/" << rank << " :  " << f << "\n\n";
   }

   if( rank == 0 )
      return f;
   else
   {
      std::vector< logic::term > args;
      logic::context ctxt; 
      flatten( ctxt, f, op, rank, args );
      return logic::term( op, args. begin( ), args. end( ));
   }
}


void 
calc::flatten( logic::context& ctxt, const logic::term& frm, 
               logic::selector op, unsigned int rank,
               std::vector< logic::term > & into )
{
   if constexpr( false )
   {
      std::cout << "flatten " << op << "/" << rank << " : ";
      std::cout << frm << "\n\n";
   }

   auto kln = kleene_top( frm, pol_pos );

   if( kln. sel( ) == op )
   {
      auto nary = kln. view_kleene( );
      for( size_t i = 0; i != nary. size( ); ++ i )
         flatten( ctxt, nary. sub(i), op, rank, into );
      return;
   }

   if( kln. sel( ) == quantof( op ))
   {
      auto ex = kln. view_quant( );
      size_t csize = ctxt. size( );
      for( size_t i = 0; i != ex. size( ); ++ i )
         ctxt. append( ex. var(i). pref, ex. var(i). tp );  
      flatten( ctxt, ex. body( ), op, rank, into );
      ctxt. restore( csize );  
      return; 
   }

   into. push_back( quantify( quantof( op ), ctxt,
                    alternating( frm, alternation( op ), rank - 1 )));
}


bool 
calc::isalternating( const logic::term& f, 
                     logic::selector op, unsigned int rank )
{
   if( f. sel( ) == logic::op_kleene_and )
   {
      throw std::logic_error( "not implemented" );
   }

   if( f. sel( ) == logic::op_kleene_or )
   {
      auto kl = f. view_kleene( );
      for( size_t i = 0; i != kl. size( ); ++ i )
      {
         const auto* p = &kl. sub(i);

#if 0
         // If it is a Kleene exists, we replace p by the body: 

         if( p -> sel( ) == logic::op_kleene_exists )
            p = &( p -> view_quant( ). body( ));
       
         if( p -> sel( ) == logic::op_kleene_and )
         {
            if( !isinanf( *p ))
               return false;
         }
         else
         {
            if( !isliteral( *p ))
               return false;
         }
#endif
      }
      return true;
   }
   return false;
}


#if 0

size_t
calc::alternation_rank( const logic::term& f )
{
   size_t rank = 0;

   if( f. sel( ) == logic::op_kleene_or )
   {
      auto kl = f. view_kleene( );
      for( size_t i = 0; i != kl. size( ); ++ i )
      {
         const auto* p = &kl. sub(i);

         // If it is a Kleene exists, we replace p by the body:

         if( p -> sel( ) == logic::op_kleene_exists )
            p = &( p -> view_quant( ). body( ));

         if( p -> sel( ) == logic::op_kleene_and )
         {
            size_t rk = alternation_rank( *p );
            if( rk > rank )
               rank = rk; 
         }
      }
      return rank + 1;
   }

#if 0
   if( isliteral(f))
      return 0;

   size_t inc = ischange( op, f. sel( ));
      // What we will be increasing here.
 
   switch( f. sel( ))
   {
   case logic::op_kleene_and:
   case logic::op_kleene_or:
      {
         size_t max = 1;
         auto prop = f. view_kleene( );
         for( size_t i = 0; i != prop. size( ); ++ i )
         {
            size_t m = alternation_rank( prop. sub(i), f. sel( )); 
            if( m > max )
               max = m;
         }
        
         return max + inc; 
      }
 
   case logic::op_kleene_forall:
   case logic::op_kleene_exists:
      {
         auto quant = f. view_quant( );

         size_t sub = alternation_rank( quant. body( ), f. sel( ));
         if( sub == 0 ) 
            sub = 1;

         return sub + inc; 
      }
   default:
      throw std::logic_error( "alternation rank : should be unreachable" );

   }
#endif
   throw std::logic_error( "rank: not in ANF" );
}
#endif

#if 0

logic::term
calc::restrict_alternation( transformer& trans, logic::beliefstate& blfs,
                logic::context& ctxt, logic::term f,
                logic::selector op, unsigned int maxrank )
{
   if constexpr( false )
   {
      std::cout << "restrict alternation : " << f << "\n";
      std::cout << "   " << op << "/" << maxrank << "\n";
   }

   if( isliteral(f))
      return f;

   // If we are not a literal, then the rank is >= 1.

   bool dec = ischange( op, f. sel( ));
      // True if we are going to decrease.

   if( maxrank == 0 || ( dec && maxrank == 1 ))
   {
      auto pr = norm_debruijns(f);

      auto restr = restriction( ctxt, pr. first );
      logic::exact pred = trans. newpredsym( blfs, "p", restr );
      trans. push( std::move( restr ), pred, pr. second,
                   pol_neg, step_rank );
      return application( logic::term( logic::op_exact, pred ), pr. first );
   }

   // We check if there is a level increase:

    if( dec ) 
      -- maxrank;

   switch( f. sel( ))
   {
   case logic::op_kleene_and:
   case logic::op_kleene_or:
      {
         auto prop = f. view_kleene( );
         for( size_t i = 0; i != prop. size( ); ++ i )
         {
            prop. update_sub( i,
               restrict_alternation( trans, blfs, ctxt, prop. extr_sub(i),
                                     f. sel( ), maxrank ));
         }
         return f;
      }
  
   case logic::op_kleene_forall:
   case logic::op_kleene_exists:
      {
         auto q = f. view_quant( ); 
         size_t ss = ctxt. size( );
         for( size_t i = 0; i != q. size( ); ++ i )
            ctxt. append( q. var(i). pref, q. var(i). tp );

         q. update_body( 
                restrict_alternation( trans, blfs, ctxt, q. extr_body( ), 
                                      f. sel( ), maxrank ));

         ctxt. restore(ss);
         return f;
      }
   }

   throw std::runtime_error( "splitalt: should be not reachable" );
}

#endif
