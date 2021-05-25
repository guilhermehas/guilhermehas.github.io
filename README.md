# Guilherme Blog

[Website Link](https://guilhermehas.github.io/)

## Run the website locally

To run the website locally, just run this command:

```sh
nix run github:guilhermehas/guilhermehas.github.io.#"guilherme-blog:exe:site" watch
```

And go to `http://127.0.0.1:8000`

## Build the website's static files

Just run:

```sh
nix build github:guilhermehas/guilhermehas.github.io
```