
#include "alternating.h"
#include "util.h"


bool calc::isatom( const logic::term& f )
{
   switch( f. sel( ))
   {
   case logic::op_not:
   case logic::op_prop:
   case logic::op_kleene_forall:
   case logic::op_kleene_exists:
   case logic::op_kleene_and:
   case logic::op_kleene_or:
      return false;
   default:
      return true;
   }
}


bool calc::isliteral( const logic::term& f )
{
   const auto* p = &f;
   if( p -> sel( ) == logic::op_not )
      p = & ( p -> view_unary( ). sub( ));

   if( p -> sel( ) == logic::op_prop )
      p = & ( p -> view_unary( ). sub( ));

   return isatom( *p );
}


logic::term calc::alt_disj( logic::term f )
{
   std::cout << "alt disj: " << f << "\n";

   std::vector< logic::term > disj;
   logic::context ctxt; 
   flatten_disj( ctxt, f, disj );
   return logic::term( logic::op_kleene_or, disj. begin( ), disj. end( ));
}


void 
calc::flatten_disj( logic::context& ctxt, const logic::term& f, 
                    std::vector< logic::term > & into )
{
   if( f. sel( ) == logic::op_kleene_or )
   {
      auto kl = f. view_kleene( );
      for( size_t i = 0; i != kl. size( ); ++ i )
         flatten_disj( ctxt, kl. sub(i), into );
      return;
   }

   if( f. sel( ) == logic::op_kleene_exists )
   {
      auto ex = f. view_quant( );
      size_t csize = ctxt. size( );
      for( size_t i = 0; i != ex. size( ); ++ i )
         ctxt. append( ex. var(i). pref, ex. var(i). tp );  
      flatten_disj( ctxt, ex. body( ), into );
      ctxt. restore( csize );  
      return; 
   }

   if( isliteral(f))
   {
      into. push_back( quantify( logic::op_kleene_exists, ctxt, f ));
      return;
   }

   if( f. sel( ) == logic::op_kleene_forall ||
       f. sel( ) == logic::op_kleene_and )
   {
      into. push_back( quantify( logic::op_kleene_exists, ctxt,
                                 alt_conj(f)));
      return;
   }

   throw std::runtime_error( "alt_conj: formula not in KNF" );
}

logic::term calc::alt_conj( logic::term f )
{
   std::cout << "alt conj: " << f << "\n";

   std::vector< logic::term > conj;
   logic::context ctxt;
   flatten_conj( ctxt, f, conj );

   return logic::term( logic::op_kleene_and, conj. begin( ), conj. end( ));
}


void
calc::flatten_conj( logic::context& ctxt, const logic::term& f,
                    std::vector< logic::term > & into )
{
   if( f. sel( ) == logic::op_kleene_and )
   {
      auto kl = f. view_kleene( );
      for( size_t i = 0; i != kl. size( ); ++ i )
         flatten_conj( ctxt, kl. sub(i), into );
      return;
   }

   if( f. sel( ) == logic::op_kleene_forall )
   {
      auto all = f. view_quant( );
      size_t csize = ctxt. size( );
      for( size_t i = 0; i != all. size( ); ++ i )
         ctxt. append( all. var(i). pref, all. var(i). tp );
      flatten_conj( ctxt, all. body( ), into );
      ctxt. restore( csize );
      return;  
   }

   if( isliteral(f))
   {
      into. push_back( quantify( logic::op_kleene_forall, ctxt, f ));
      return;
   }

   if( f. sel( ) == logic::op_kleene_exists || 
       f. sel( ) == logic::op_kleene_or )
   {
      into. push_back( quantify( logic::op_kleene_forall, ctxt,
                                 alt_disj(f))); 
      return;
   }

   throw std::runtime_error( "alt_conj: formula not in KNF" );
}


namespace
{
   // If we have change from (forall/and) to (exists/or):

   bool ischange( logic::selector op1, logic::selector op2 )
   {
      if( op1 == logic::op_kleene_forall )
         op1 = logic::op_kleene_and;
      if( op1 == logic::op_kleene_exists )
         op1 = logic::op_kleene_or;

      if( op2 == logic::op_kleene_forall )
         op2 = logic::op_kleene_and;
      if( op2 == logic::op_kleene_exists )
         op2 = logic::op_kleene_or;

      return op1 != op2; 
   }
}

bool calc::isinanf( const logic::term& f )
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
      }
      return true;
   }
   return false;
}

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

