
#include "clauseset.h"
#include "logic/cmp.h"
#include "logic/replacements.h"


void calc::clauseset::insert( const logic::term& tm )
{
   switch( tm. sel( ))
   {
   case logic::op_kleene_and:
      {
         auto kl = tm. view_kleene( );
         for( size_t i = 0; i != kl. size( ); ++ i )
            insert( kl. sub(i));
         return; 
      }

   case logic::op_kleene_or:
      {
         auto kl = tm. view_kleene( );
         auto clause = std::list< logic::term > ( );
         for( size_t i = 0; i != kl. size( ); ++ i )
            clause. push_back( kl. sub(i));
         set. push_back( std::move( clause ));
         return;
      }

   case logic::op_kleene_forall:
      {
         auto quant = tm. view_quant( );
         if( quant. size( ) == 0 )
            insert( quant. body( ));
         return;
      }
         
   }

   std::cout << "clauseset::insert " << tm. sel( ) << "\n";
   throw std::logic_error( "insert: unknown selector type" );

   auto kl = tm. view_kleene( );
   for( size_t i = 0; i != kl. size( ); ++ i )
   {
      if( kl. sub(i). sel( ) != logic::op_kleene_or )
         return;

      auto cls = kl. sub(i). view_kleene( );
      set. push_back( std::list< logic::term > ( ));
      for( size_t j = 0; j != cls. size( ); ++ j )
         set. back( ). push_back( cls. sub(j));
   }

   return; 
}

uint64_t calc::clauseset::res_simplify( )
{
   uint64_t counter = 0;

   for( auto from = set. begin( ); from != set. end( ); ++ from )
   {
      for( auto into = set. begin( ); into != set. end( ); ++ into ) 
      {
         if( into != from )
         {
            for( auto p = from -> begin( ); p != from -> end( ); ++ p )
            {
               auto in = into -> begin( ); 
               while( in != into -> end( ))
               {
                  if( inconflict( *p, *in ) && subset( *from, p, *into, in )) 
                  {
                     std::cout << *p << " conflicts " << *in << "\n";
                     in = into -> erase( in );
                     ++ counter; 
                  }
                  else 
                     ++ in;
               }
            }
         } 
      }
   }

   return counter;
}


uint64_t calc::clauseset::eq_simplify( )
{
   uint64_t counter = 0;

   for( auto from = set. begin( ); from != set. end( ); ++ from )
   {
      for( auto into = set. begin( ); into != set. end( ); ++ into )
      {
         if( into != from )
         {
            for( auto eq = from -> begin( ); eq != from -> end( ); ++ eq )
            {
               if( eq -> sel( ) == logic::op_equals )
               {
                  auto rewr = logic::rewriterule( 
                     eq -> view_binary( ). sub1( ), 
                     eq -> view_binary( ). sub2( ));
                  
                  std::cout << rewr << "\n";
                  auto cmp = kbo( rewr. from, rewr. to );

                  if( !is_eq( cmp ))
                  {
                     if( is_lt( cmp ))
                        rewr. swap( );
                     std::cout << "directed: " << rewr << "\n";

                     for( auto in = into -> begin( ); 
                          in != into -> end( ); ++ in ) 
                     {
                        // We first check for subset.
                        // If yes, we try to rewrite, and count
                        // how often it happened.

                        if( subset( *from, eq, *into, in ))
                        {
                           rewr. counter = 0;
                           *in = outermost( rewr, *in, 0 );
                           counter += rewr. counter; 
                        }
                     }
                  }
               }
            }
         }
      }
   }

   return counter;
}

uint64_t 
calc::clauseset::fully_simplify( )
{
   remove_repeated( );
   remove_redundant( );
   uint64_t counter = 0;
restart:
   auto s = res_simplify( ) + eq_simplify( );
   if(s) 
   {
      counter += s;
      goto restart;
   }
   remove_repeated( );
   remove_redundant( );

   return counter;
}

void calc::clauseset::remove_repeated( )
{
   for( auto& cl : set )
      calc::remove_repeated( cl ); 
}

void calc::clauseset::remove_redundant( )
{
   // First remove tautologies:

   auto it = set. begin( );
   while( it != set. end( ))
   {
      if( istautology( *it ))
         it = set. erase( it );
      else
         ++ it;
   }

   // Then subsumed:

   for( auto it = set. begin( ); it != set. end( ); ++ it )
   {
      auto p = set. begin( );
      while( p != set. end( ))
      {
         if( p != it && subset( *it, it -> end( ), *p, p -> end( )))
            p = set. erase(p);
         else
            ++ p;
      }
   }
}


logic::term
calc::clauseset::getformula( ) const
{
   auto res = logic::term( logic::op_kleene_and,
                           std::initializer_list< logic::term > ( ));
   auto kl = res. view_kleene( );
   for( const auto& cl : set )
      kl. push_back( disjunction( cl )); 
   return res;
}

void
calc::clauseset::print( std::ostream& out ) const
{
   out << "Clause Set:\n";
   for( const auto& cls : set )
   {
      out << "   ";
      if( cls. size( ) > 0 )
      {
         for( auto p = cls. begin( ); p != cls. end( ); ++ p )
         {
            if( p != cls. begin( ))
               out << ", ";
            out << *p;
         }
      }
      else
         out << "(empty)";
      out << "\n";
   }
   out << "\n";
}

bool
calc::inconflict( short int pol1, const logic::term& tm1,
                  short int pol2, const logic::term& tm2 )
{
   // std::cout << pol1 << "  " << tm1 << "   " << pol2 << "  " << tm2 << "\n";

   if( pol1 > 0 && pol2 < 0 && logic::equal( tm1, tm2 ))
      return true;

   if( pol1 < 0 && pol2 > 0 && logic::equal( tm1, tm2 ))
      return true;

   if( pol1 < 0 && tm1. sel( ) == logic::op_prop &&
       logic::equal( tm1. view_unary( ). sub( ), tm2 ))
   {
      return true;
   }

   if( pol2 < 0 && tm2. sel( ) == logic::op_prop &&
       logic::equal( tm1, tm2. view_unary( ). sub( )) )
   {
      return true;
   }

   return false;
}


bool
calc::inconflict( const logic::term& tm1, const logic::term& tm2 )
{
   // This is probably a point where one would like to have matching.
   // We try to bring some order in the chaos by separating out
   // negation.

   if( tm1. sel( ) == logic::op_not )
   {
      if( tm2. sel( ) == logic::op_not )
      {
         return inconflict( -1, tm1. view_unary( ). sub( ),
                            -1, tm2. view_unary( ). sub( ));
      }
      else
         return inconflict( -1, tm1. view_unary( ). sub( ), 1, tm2 );
   }
   else
   {
      if( tm2. sel( ) == logic::op_not )
         return inconflict( 1, tm1, -1, tm2. view_unary( ). sub( ) );
      else
         return inconflict( 1, tm1, 1, tm2 );
   }
}

bool 
calc::contains( const logic::term& lit, 
                const clause& cls, clause::const_iterator skip )
{
   for( auto q = cls. begin( ); q != cls. end( ); ++ q )
   {
      if( q != skip && equal( lit, *q ))
         return true;
   } 
   
   return false;
}

bool 
calc::subset( const clause& cls1, clause::const_iterator skip1,
              const clause& cls2, clause::const_iterator skip2 )
{
   for( auto p1 = cls1. begin( ); p1 != cls1. end( ); ++ p1 )
   {
      if( p1 != skip1 && !contains( *p1, cls2, skip2 ))
         return false;
   }
   return true; 
}

bool
calc::certainly( short int pol, const logic::term& tm )
{
   if( tm. sel( ) == logic::op_not )
   {
      auto un = tm. view_unary( );
      return certainly( -pol, un. sub( ));
   }

   if( pol > 0 && tm. sel( ) == logic::op_prop )
   {
      auto un = tm. view_unary( ); 
      if( un. sub( ). sel( ) == logic::op_equals ||
          un. sub( ). sel( ) == logic::op_prop )
      {
         return true;
      }
   }

   if( pol > 0 && tm. sel( ) == logic::op_equals ) 
   {
      auto eq = tm. view_binary( );
      if( equal( eq. sub1( ), eq. sub2( )))
         return true;
   }

   return false;
}

void calc::remove_repeated( clause& cls ) 
{
   auto it = cls. begin( );
   while( it != cls. end( ))
   {
      bool skip = false;

      if( certainly( -1, *it ))
         skip = true;

      for( auto p = cls. begin( ); p != it && !skip; ++ p )
      {
         if( equal( *p, *it ))
            skip = true;
      }

      if( skip )
         it = cls. erase( it );
      else
         ++ it;
   }
}

bool
calc::istautology( const clause& cls )
{
   for( const auto& lit : cls ) 
   {
      if( certainly( 1, lit ))
         return true;
   }
   return false;
}

logic::term
calc::disjunction( const clause& cls )
{
   logic::term res = logic::term( logic::op_kleene_or, 
                                  std::initializer_list< logic::term > ( )); 
   auto kl = res. view_kleene( );
   for( const auto& lit : cls )
      kl. push_back( lit ); 
   return res;
}

