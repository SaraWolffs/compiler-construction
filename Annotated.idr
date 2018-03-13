module Annotated

import Effect.Default

%default total 
%access public export

data Annotated : (noteTy : Type) -> (baseTy : Type) -> Type where
  NotePure : (note : noteTy) -> (x : baseTy) -> Annotated noteTy baseTy
  NoteApp  : (f : Annotated noteTy (a -> b)) -> (x : Annotated noteTy a) -> 
                Annotated noteTy b

Functor (Annotated noteTy) where
  map g (NotePure note x) = NotePure note (g x)
  map g (NoteApp f x) = NoteApp (map (g .) f) x

(Monoid noteTy) => Applicative (Annotated noteTy) where
  pure = NotePure neutral
  (<*>)  = NoteApp


stripNotes : Annotated _ a -> a
stripNotes (NotePure note x) = x
stripNotes (NoteApp f x) = stripNotes f $ stripNotes x
