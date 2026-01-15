# LogOS: an Agda research library for foundational logic system architecture.
# Copyright (C) 2026 AI.IMPACT GmbH
# SPDX-License-Identifier: GPL-3.0-only

import tensorflow as tf

def build_model(vocab_size, d_model, n_heads, n_layers, d_ff, max_len, dropout):
    tok_in = tf.keras.Input(shape=(None,), dtype=tf.int32, name="tokens")
    tok_emb = tf.keras.layers.Embedding(vocab_size, d_model)(tok_in)
    pos = tf.range(tf.shape(tok_in)[1])
    pos_emb = tf.keras.layers.Embedding(max_len, d_model)(pos)
    x = tok_emb + pos_emb
    for _ in range(n_layers):
        attn = tf.keras.layers.MultiHeadAttention(num_heads=n_heads, key_dim=d_model // n_heads, dropout=dropout, use_causal_mask=True)(x, x)
        x = tf.keras.layers.LayerNormalization(epsilon=1e-5)(x + attn)
        ffn = tf.keras.layers.Dense(d_ff, activation="relu")(x)
        ffn = tf.keras.layers.Dense(d_model)(ffn)
        x = tf.keras.layers.LayerNormalization(epsilon=1e-5)(x + ffn)
    logits = tf.keras.layers.Dense(vocab_size)(x)
    return tf.keras.Model(tok_in, logits)

def train(model, dataset, epochs, learning_rate):
    # dataset yields (input, target)
    loss_fn = tf.keras.losses.SparseCategoricalCrossentropy(from_logits=True, reduction="none")
    optimizer = tf.keras.optimizers.Adam(learning_rate)
    for epoch in range(epochs):
        for (x, y) in dataset:
            with tf.GradientTape() as tape:
                logits = model(x, training=True)
                loss = tf.reduce_mean(loss_fn(y, logits))
            grads = tape.gradient(loss, model.trainable_variables)
            optimizer.apply_gradients(zip(grads, model.trainable_variables))