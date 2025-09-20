
#include "clauseset.h"
#include "logic/cmp.h"
#include "logic/replacements.h"


bool 
calc::clauseset::insert( const logic::term& tm )
{
   if( tm. sel( ) != logic::op_kleene_and )
      return false;

   auto kl = tm. view_kleene( );
   for( size_t i = 0; i != kl. size( ); ++ i )
   {
      if( kl. sub(i). sel( ) != logic::op_kleene_or )
         return false;

      auto cls = kl. sub(i). view_kleene( );
      set. push_back( std::list< logic::term > ( ));
      for( size_t j = 0; j != cls. size( ); ++ j )
         set. back( ). push_back( cls. sub(j));
   }

   return true; 
}

void 
calc::clauseset::res_simplify( )
{
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
                     std::cout << *p << " <#> " << *in << "\n";
                     in = into -> erase( in );
                  }
                  else 
                     ++ in;
               }
            }
         } 
      }
   }
}


void calc::clauseset::eq_simplify( )
{
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
                        // If yes, we rewrite without checking if
                        // a replacement was made.

                        if( subset( *from, eq, *into, in ))
                        {
                           std::cout << "attempting to rewrite " << *in << "\n";
                           *in = outermost( rewr, *in, 0 );
                        } 
                     }
                  }
               }
            }
         }
      }
   }
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
calc::contains( const logic::term& lit, const clauseset::clause& cls,
                clauseset::clause::const_iterator skip )
{
   std::cout << "      contains " << lit << " skip " << *skip << "\n";

   for( auto q = cls. begin( ); q != cls. end( ); ++ q )
   {
      if( q != skip && equal( lit, *q ))
         return true;
   } 
   
   return false;
}

bool 
calc::subset( const clauseset::clause& cls1,
              clauseset::clause::const_iterator skip1,
              const clauseset::clause& cls2,
              clauseset::clause::const_iterator skip2 )
{
   for( auto p1 = cls1. begin( ); p1 != cls1. end( ); ++ p1 )
   {
      if( p1 != skip1 && !contains( *p1, cls2, skip2 ))
         return false;
   }
   return true; 
}

logic::term
calc::merge( const logic::term& form1, size_t skip1,
             const logic::term& form2, size_t skip2 )
{
   if( !form1. option_is_kleene( ))
      throw std::logic_error( "calc::merge: Not a Kleene operator" );

   if( form1. sel( ) != form2. sel( ))
      throw std::logic_error( "calc::merge: Operators differ" );

   auto res = 
      logic::term( form1. sel( ), std::initializer_list< logic::term > ( ));

   auto kl = res. view_kleene( ); 

   auto kl1 = form1. view_kleene( );
   for( size_t i = 0; i != kl1. size( ); ++ i )
   {
#if 0
      if( i != skip1 && !contains( kl1. sub(i), res, kl. size( ) ))
         kl. push_back( kl1. sub(i));
#endif
   }

   auto kl2 = form2. view_kleene( );
   for( size_t i = 0; i != kl2. size( ); ++ i )
   {
#if 0
      if( i != skip2 && !contains( kl2. sub(i), res, kl. size( ) ))
         kl. push_back( kl2. sub(i));
#endif
   }

   return res;      
}

void
calc::clauseset::print( std::ostream& out ) const
{
   out << "Clause Set:\n";
   for( const auto& cls : set )
   {
      out << "   ";
      for( auto p = cls. begin( ); p != cls. end( ); ++ p )
      {
         if( p != cls. begin( ))
            out << ", ";
         out << *p;
      }
      out << "\n";
   }
   out << "\n";
}

