{-# LANGUAGE OverloadedStrings #-}

import Hakyll
  ( Context,
    applyAsTemplate,
    compile,
    compressCssCompiler,
    constField,
    copyFileCompiler,
    create,
    dateField,
    defaultContext,
    field,
    getResourceBody,
    hakyll,
    idRoute,
    listField,
    loadAll,
    loadAndApplyTemplate,
    loadBody,
    makeItem,
    match,
    pandocCompiler,
    recentFirst,
    relativizeUrls,
    route,
    setExtension,
    templateBodyCompiler,
  )

postCtx :: Context String
postCtx = dateField "date" "%B %e, %Y" <> defaultContext

main :: IO ()
main = hakyll $ do
  match "images/*" $ do
    route idRoute
    compile copyFileCompiler

  match "css/*" $ do
    route idRoute
    compile compressCssCompiler

  match "publications.md" $ do
    route $ setExtension "html"
    compile $
      pandocCompiler
        >>= loadAndApplyTemplate "templates/default.html" defaultContext
        >>= relativizeUrls

  match "about-contact.md" $ compile pandocCompiler

  match "posts/*.md" $ do
    route $ setExtension "html"
    compile $
      pandocCompiler
        >>= loadAndApplyTemplate "templates/post.html" postCtx
        >>= loadAndApplyTemplate "templates/default.html" postCtx
        >>= relativizeUrls

  create ["posts.html"] $ do
    route idRoute
    compile $ do
      posts <- loadAll "posts/*.md" >>= recentFirst
      let postsCtx =
            listField "posts" postCtx (pure posts)
              <> constField "title" "Posts"
              <> defaultContext

      makeItem ""
        >>= loadAndApplyTemplate "templates/posts.html" postsCtx
        >>= loadAndApplyTemplate "templates/default.html" postsCtx
        >>= relativizeUrls

  match "index.html" $ do
    route idRoute
    compile $ do
      aboutContent <- loadBody "about-contact.md"
      let indexCtx =
            field "about" (const $ pure aboutContent)
              <> defaultContext

      getResourceBody
        >>= applyAsTemplate indexCtx
        >>= loadAndApplyTemplate "templates/default.html" indexCtx
        >>= relativizeUrls

  match "templates/*" $ compile templateBodyCompiler
