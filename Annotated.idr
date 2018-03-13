module Annotated

import Control.Pipeline

%default total 
%access public export

data Annotated : (noteTy : Type) -> (baseTy : Type) -> Type where
  Annotate : (note : noteTy) -> (x : baseTy) -> Annotated noteTy baseTy
  NotePure : (x : baseTy) -> Annotated _ baseTy
  NoteApp  : (f : Annotated noteTy (a -> b)) -> (x : Annotated noteTy a) -> 
                Annotated noteTy b

Functor (Annotated noteTy) where
  map g (Annotate note x) = Annotate note (g x)
  map g (NotePure x) = NotePure (g x)
  map g (NoteApp f x) = NoteApp (map (g .) f) x
  

Applicative (Annotated noteTy) where
  pure = NotePure 
  (NotePure f) <*> x = map f x
  f <*> (NotePure x) = map (<| x) f
  f <*> x = NoteApp f x

stripNotes : Annotated _ a -> a
stripNotes (NotePure x) = x
stripNotes (NoteApp f x) = stripNotes f $ stripNotes x
stripNotes (Annotate note x) = x
