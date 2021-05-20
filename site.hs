--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Control.Monad
-- import           Control.Monad.Extra

import           Data.List
import           Data.Monoid
import           Data.String

import           Hakyll
import           Hakyll.Core.UnixFilter
import           Hakyll.Web.Pandoc.Biblio

-- import           System.Directory
import           System.Exit
-- import           System.FilePath
-- import           System.Process

-- import           Text.Pandoc.Options

import qualified GHC.IO.Encoding as E


--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match (fromList ["about.rst", "contact.markdown"]) $ do
        route   $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    match "posts/*" $ do
        route $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/post.html"    postCtx
            >>= loadAndApplyTemplate "templates/default.html" postCtx
            >>= relativizeUrls

    create ["archive.html"] $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            let archiveCtx =
                    listField "posts" postCtx (return posts) `mappend`
                    constField "title" "Archives"            `mappend`
                    defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/archive.html" archiveCtx
                >>= loadAndApplyTemplate "templates/default.html" archiveCtx
                >>= relativizeUrls


    match "index.html" $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            let indexCtx =
                    listField "posts" postCtx (return posts) `mappend`
                    defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    match "templates/*" $ compile templateBodyCompiler


--------------------------------------------------------------------------------
postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext

--------------------------------------------------------------------------------

-- agdaCommand :: String
-- agdaCommand = "agda"

-- agdaInputDir :: String
-- agdaInputDir = "agda-posts"

-- agdaOutputDir :: String
-- agdaOutputDir = "_agda"

-- agdaOptions :: String -> [String]
-- agdaOptions fileName =
--   [ "--html"
--   , "--html-highlight=auto"
--   , "--html-dir=" ++ agdaOutputDir
--   , "-i" ++ agdaInputDir
--   , agdaInputDir </> fileName
--   ]

-- -- Process a .lagda.md file into markdown by calling Agda
-- processAgdaPosts :: IO ()
-- processAgdaPosts = do
--   files <- listDirectory agdaInputDir
--   let agdaFiles = filter (".lagda.md" `isSuffixOf`) files
--   forM_ agdaFiles processAgdaPost

-- processAgdaPost :: FilePath -> IO ()
-- processAgdaPost agdaFile = do
--   exitCode <- readProcessWithExitCode agdaCommand (agdaOptions agdaFile) mempty
--   case exitCode of
--     (ExitFailure _ , err , _) -> do
--       putStrLn $ "Failed to process " ++ agdaFile
--       putStrLn err
--     (ExitSuccess   , out , _) -> do
--       putStrLn out
