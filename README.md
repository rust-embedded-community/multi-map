# Multi-Map

[![Build Status](https://travis-ci.org/thejpster/multi-map.svg?branch=master)](https://travis-ci.org/thejpster/multi-map)
[![Crate version](https://img.shields.io/crates/v/multi-map.svg)](https://crates.io/crates/multi-map)
[![Documentation](https://img.shields.io/badge/documentation-docs.rs-df3600.svg)](https://docs.rs/multi-map)

Like a `std::collection::HashMap`, but allows you to use either of two different keys to retrieve items.

Sometimes, when developing software stacks, a layer will have some context object it needs to store. Assume, for example, we have an HTTP module, which sits below some sort of HTTP-using Application, and above a Socket module.

When a new connection is created, a message is received from the Socket module with the ID of the new connection. A new HTTP Connection object is created, and stored against the Socket ID, so that it can be easily retrieved when data arrives on the Socket. But to inform the layer above about the new HTTP Connection (as distinct from any other HTTP Connections that may be on going), we need to give the HTTP Connection itself a unique ID, and we need some mechanism of locating the HTTP Connection by this ID as well.

The trivial solution is to store the HTTP Connections in a list, and then iterate them, looking for a matching Socket ID or a matching HTTP Connection ID. But this is slow.

A HashMap seems like a good idea, but you can only key on either the HTTP ID or the Socket ID, not on both.

This module allows you to create a MultiMap - a map which you can look up either by the primary key (HttpID) or an alternative ID (SocketID). Internally, it uses two maps, one on (K1, (K2, V)) and another on (K2, K1).

Insert, removal and iteration is supported. Gradually, I might implement the rest of the std::collections::HashMap API, but I've found this to be sufficiently useful for now.
